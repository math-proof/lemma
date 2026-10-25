/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KPerfect.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!
# Parameterized perfect numbers

A positive natural number `n` is `k`-perfect when its sum of positive divisors is `k * n`.

## References

* Yoshinosuke Hirakawa, *A note on the Diophantine equation
  2ℓn² = 1 + q + ⋯ + q^α and application to odd perfect numbers*, arXiv:2309.17084v3
-/


namespace Nat

/-- A positive natural number is `k`-perfect when its divisor sum is `k` times the number. -/
def IsKPerfect (k n : ℕ) : Prop :=
  0 < n ∧ (ArithmeticFunction.sigma 1) n = k * n

end Nat
