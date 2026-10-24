import Mathlib
import sympy.Basic


namespace Integers

/--
[ideal_span_pair_eq_span_gcd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Integers.lean)
-/
@[path]
lemma ideal_span_pair_eq_span_gcd
  {a b : ℤ} :
-- imply
  Ideal.span {a, b} = Ideal.span {(Int.gcd a b : ℤ)} := by
-- proof
  rw [Int.coe_gcd]
  exact (span_gcd a b).symm

end Integers


-- created on 2026-10-23
