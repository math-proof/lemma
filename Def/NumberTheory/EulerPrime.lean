/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean -/

import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc


namespace MetaMathlibExt

/-- Full witnessed Eulerian form of an odd perfect number:
perfectness, oddness, primality of `q`, the factorization
`N = q ^ k * n ^ 2`, both congruences `q ≡ 1 (mod 4)`,
`k ≡ 1 (mod 4)`, and coprimality of `q` and `n`. -/
def EulerianForm (N q k n : ℕ) : Prop :=
  Nat.Perfect N ∧ Odd N ∧ Nat.Prime q ∧ N = q ^ k * n ^ 2 ∧
    q % 4 = 1 ∧ k % 4 = 1 ∧ Nat.Coprime q n

/-- `q` is an Euler prime of `N` iff some `k, n` witness the full form.
No choice function is defined since existence of odd perfect numbers is open. -/
def IsEulerPrime (N q : ℕ) : Prop :=
  ∃ k n, EulerianForm N q k n

end MetaMathlibExt
