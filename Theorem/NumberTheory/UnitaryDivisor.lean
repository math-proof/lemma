/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.Divisors
public import Def.NumberTheory.UnitaryDivisor

/-!
# Unitary divisors

Reusable definitions for unitary divisors, their sum, and divisibility-minimal
members of sets of natural numbers.
-/

public section


namespace Nat

theorem dvd_of_mem_unitaryDivisors {n d : ℕ} (h : d ∈ unitaryDivisors n) : d ∣ n :=
  (mem_unitaryDivisors.mp h).1

end Nat
