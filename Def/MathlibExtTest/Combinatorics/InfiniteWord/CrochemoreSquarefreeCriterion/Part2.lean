/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/CrochemoreSquarefreeCriterion.lean -/


import Lemma.Finset.InfiniteWord.CrochemoreSquarefreeCriterion
import Mathlib.Tactic
import Theorem.MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion


namespace MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion

open MetaMathlibExt

/-- A morphism whose image of `010` contains the square `2020`. -/
def failingMorphism : TernaryAlphabet → List TernaryAlphabet
  | 0 => [0, 1, 2]
  | 1 => [0, 2]
  | 2 => [1]

end MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion
