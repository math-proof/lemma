/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/CrochemoreSquarefreeCriterion.lean -/


import Lemma.Finset.InfiniteWord.CrochemoreSquarefreeCriterion
import Mathlib.Tactic
import Def.MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion


namespace MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion

open MetaMathlibExt

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in

-- The length-five test proves that the concrete nonuniform morphism preserves squarefreeness.
example : ∀ w : List TernaryAlphabet, IsSquareFreeWord w →
    IsSquareFreeWord (w.flatMap shortSquarefreeMorphism) :=
  (crochemore_squarefree_test_set shortSquarefreeMorphism).2
    shortSquarefreeMorphism_test

end MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion
