import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.LiouvilleDivisorIdentity
open scoped BigOperators
open MetaMathlibExt


/--
[liouville_divisor_function_identity_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma liouville_divisor_function_identity_general_eq
  {n : ℕ} :
-- imply
  (∑ d ∈ n.divisors, d.divisors.card) ^ 2 =
    ∑ d ∈ n.divisors, (d.divisors.card) ^ 3 := by
-- proof
  apply MetaMathlibExt.liouville_divisor_function_identity_general n

/--
[liouville_divisor_function_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/LiouvilleDivisorIdentity.lean)
-/
@[path]
private lemma liouville_divisor_function_identity_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ d ∈ n.divisors, d.divisors.card) ^ 2 =
    ∑ d ∈ n.divisors, (d.divisors.card) ^ 3 := by
-- proof
  apply MetaMathlibExt.liouville_divisor_function_identity n hn


-- created on 2026-10-20
