/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/CrochemoreSquarefreeCriterion.lean -/


import Lemma.Finset.InfiniteWord.CrochemoreSquarefreeCriterion

import Mathlib.Tactic


namespace MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion

open MetaMathlibExt

/-- A concrete nonuniform ternary morphism used to exercise the finite test. -/
def shortSquarefreeMorphism : TernaryAlphabet → List TernaryAlphabet
  | 0 => [0, 1, 2, 0, 1]
  | 1 => [0, 2, 0, 1, 2, 1]
  | 2 => [0, 2, 1, 2, 0, 2, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in

-- The length-five test proves that the concrete nonuniform morphism preserves squarefreeness.
example : ∀ w : List TernaryAlphabet, IsSquareFreeWord w →
    IsSquareFreeWord (w.flatMap shortSquarefreeMorphism) :=
  (crochemore_squarefree_test_set shortSquarefreeMorphism).2
    shortSquarefreeMorphism_test

/-- A morphism whose image of `010` contains the square `2020`. -/
def failingMorphism : TernaryAlphabet → List TernaryAlphabet
  | 0 => [0, 1, 2]
  | 1 => [0, 2]
  | 2 => [1]

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
