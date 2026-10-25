/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Divisors
/-!
# Unitary divisors

Reusable definitions for unitary divisors, their sum, and divisibility-minimal
members of sets of natural numbers.
-/


namespace Nat

/-- The unitary divisors of `n`: divisors coprime to their complementary divisors. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => d.Coprime (n / d)

end Nat
