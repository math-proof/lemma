import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.GcdSumTotient
open MetaMathlibExt


/--
[gcd_sum_eq_totient_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/GcdSumTotient.lean)
-/
@[path]
private lemma gcd_sum_eq_totient_sum_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ j ∈ Finset.Icc 1 n, (Nat.gcd j n : ℚ)) =
    (n : ℚ) * ∑ d ∈ Nat.divisors n, (Nat.totient d : ℚ) / (d : ℚ) := by
-- proof
  apply MetaMathlibExt.gcd_sum_eq_totient_sum n hn


-- created on 2026-10-20
