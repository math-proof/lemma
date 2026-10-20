import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.SquareFibonacciLucas
open MetaMathlibExt


/--
[cohn_square_lucas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma cohn_square_lucas_eq
  {n x : ℕ}
-- given
  (hn : 0 < n)
  (h : lucasNumber n = x ^ 2) :
-- imply
  n = 1 ∨ n = 3 := by
-- proof
  apply MetaMathlibExt.cohn_square_lucas n x hn h


-- created on 2026-10-20
