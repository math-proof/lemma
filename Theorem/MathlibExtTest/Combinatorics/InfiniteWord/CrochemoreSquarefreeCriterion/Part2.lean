/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/CrochemoreSquarefreeCriterion.lean -/


import Lemma.Finset.InfiniteWord.CrochemoreSquarefreeCriterion
import Mathlib.Tactic
import Def.MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion.Part2


namespace MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion

open MetaMathlibExt

-- Infix closure applies nontrivially, while `010` witnesses failure of the other morphism.
example (h : IsSquareFreeWord ([0, 1, 2] : List TernaryAlphabet)) :
    IsSquareFreeWord ([1, 2] : List TernaryAlphabet) ∧
      ¬ IsSquareFreeWord (([0, 1, 0] : List TernaryAlphabet).flatMap failingMorphism) := by
  constructor
  · exact h.of_isInfix ⟨[0], [], by simp⟩
  · intro hout
    apply hout [2, 0, 2, 0]
    · exact ⟨[0, 1], [1, 2], by decide⟩
    · exact ⟨[2, 0], by simp, rfl⟩

end MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion
