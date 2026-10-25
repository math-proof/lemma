/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Order.Interval.Set.Nat
/-!
# Socialist primes

Definition from Trudgian, *There are no socialist primes less than 10^9*,
arXiv:1310.6403v2, line 24:

> Erdős asked whether there exist any primes $p>5$ for which the numbers
> $2!, 3!, \ldots, (p-1)!$ are all distinct modulo $p$.

A socialist prime is a prime `p > 5` such that the natural residues
`k ! % p` for `k ∈ Set.Icc 2 (p-1)` are pairwise distinct.
Equality of natural remainders is equivalent to congruence mod `p` for `p>0`.
-/


namespace Nat

/-- A natural number `p` is a socialist prime iff `p` is prime, `5 < p`,
and the factorials `k! % p` for `k ∈ [2, p-1]` are pairwise distinct.
Trudgian, arXiv:1310.6403v2, line 24. -/
def IsSocialistPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ 5 < p ∧
    Set.Pairwise (Set.Icc 2 (p - 1)) (fun k l => k.factorial % p ≠ l.factorial % p)

end Nat
