/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Defs
/-!
# Alder's totient with second argument fixed at 2

From arXiv:2608.00889v1 `main.tex` lines 294–297: for `k ≥ 1`,
`g(k) = |{ 0 ≤ r < k | gcd(k,r)=gcd(k,2r+1)=1 }|`.
We define `alderTotientTwo k` as the cardinality of `r ∈ Finset.range k`
satisfying `Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)`.
The same formula extends to `k = 0` with `Finset.range 0 = ∅` and value `0`,
as required by `ArithmeticFunction` (`map_zero'`).
-/


namespace ArithmeticFunction

/-- Alder's extension of Euler's totient with second argument `2`.

Counts `r < k` with `gcd(k,r)=1` and `gcd(k,2r+1)=1`.
At `k = 0` the range is empty, with value `0`. -/
def alderTotientTwo : ArithmeticFunction ℕ where
  toFun k :=
    ((Finset.range k).filter fun r =>
      Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)).card
  map_zero' := by simp

end ArithmeticFunction
