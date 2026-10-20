import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LucasSequence
open MetaMathlibExt


/--
[lucasU_fibonacciLucasParams](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSequence.lean)
-/
@[path]
private lemma lucasU_fibonacciLucasParams_eq
  {n : ℕ} :
-- imply
  lucasU fibonacciLucasParams n = (Nat.fib n : ℤ) := by
-- proof
  apply MetaMathlibExt.lucasU_fibonacciLucasParams n

/--
[lucasV_fibonacciLucasParams](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSequence.lean)
-/
@[path]
private lemma lucasV_fibonacciLucasParams_eq
  {n : ℕ} :
-- imply
  lucasV fibonacciLucasParams n = (lucasNumber n : ℤ) := by
-- proof
  apply MetaMathlibExt.lucasV_fibonacciLucasParams n


-- created on 2026-10-20
