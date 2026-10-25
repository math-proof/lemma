/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Divisors
import Def.NumberTheory.UnitaryDivisor
/-!
# Unitary divisors

Reusable definitions for unitary divisors, their sum, and divisibility-minimal
members of sets of natural numbers.
-/


namespace Nat

theorem dvd_of_mem_unitaryDivisors {n d : ℕ} (h : d ∈ unitaryDivisors n) : d ∣ n :=
  (mem_unitaryDivisors.mp h).1

end Nat
