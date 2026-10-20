import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion
open MetaMathlibExt


/--
[crochemore_squarefree_test_set](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/CrochemoreSquarefreeCriterion.lean)
-/
@[path]
private lemma crochemore_squarefree_test_set_eq
  {f : TernaryAlphabet → List T} :
-- imply
  (∀ w : List TernaryAlphabet, IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f)) ↔
    ∀ w : List TernaryAlphabet, w.length ≤ 5 →
    IsSquareFreeWord w → IsSquareFreeWord (w.flatMap f) := by
-- proof
  apply MetaMathlibExt.crochemore_squarefree_test_set f


-- created on 2026-10-20
