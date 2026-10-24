/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GibonacciNumber.lean -/


import sympy.atlas.NumberTheory.GibonacciNumber
import Lemma.Nat.GibonacciNumber
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : gibonacciNumber 3 4 5 = 29 := by
  norm_num [gibonacciNumber]

example : gibonacciNumber 0 1 8 = 21 := by
  norm_num [gibonacciNumber]

example (n : ℕ) : gibonacciNumber 0 1 n = (Nat.fib n : ℤ) :=
  gibonacci_zero_one_eq_fib n

#print axioms gibonacciNumber
#print axioms gibonacci_zero_one_eq_fib

end MetaMathlibExt
