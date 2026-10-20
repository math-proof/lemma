import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.FibonacciFiveAdicValuation
open MetaMathlibExt


/--
[lengyel_fibonacci_five_adic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/FibonacciFiveAdicValuation.lean)
-/
@[path]
private lemma lengyel_fibonacci_five_adic_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  padicValNat 5 (Nat.fib n) = padicValNat 5 n := by
-- proof
  apply MetaMathlibExt.lengyel_fibonacci_five_adic n hn


-- created on 2026-10-20
