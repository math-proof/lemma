import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.CohnTwiceSquareLucas
open MetaMathlibExt


/--
[cohn_twice_square_lucas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma cohn_twice_square_lucas_eq
  {n x : ℕ}
-- given
  (hn : 0 < n)
  (h : lucasNumber n = 2 * x ^ 2) :
-- imply
  n = 6 := by
-- proof
  apply MetaMathlibExt.cohn_twice_square_lucas n x hn h


-- created on 2026-10-20
