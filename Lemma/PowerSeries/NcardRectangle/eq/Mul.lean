import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[rectangle_ncard_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n m : ℕ) :
-- imply
  (Rectangle n m).ncard = n * m := by
-- proof
  have h : Rectangle n m = Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m := by
    ext ⟨x, y⟩
    simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
    tauto
  rw [h, Set.ncard_prod]
  simp [Set.ncard_eq_toFinset_card', Set.toFinset_Icc]


-- created on 2026-10-20
