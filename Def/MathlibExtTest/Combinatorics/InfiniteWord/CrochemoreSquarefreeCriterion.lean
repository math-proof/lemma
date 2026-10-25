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

end MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion
