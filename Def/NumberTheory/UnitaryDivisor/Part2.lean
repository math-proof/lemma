/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Divisors
import Theorem.NumberTheory.UnitaryDivisor
/-!
# Unitary divisors

Reusable definitions for unitary divisors, their sum, and divisibility-minimal
members of sets of natural numbers.
-/


namespace Nat

/-- The sum of the unitary divisors of `n`, conventionally denoted `σ⋆(n)`. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

end Nat

namespace Set

/-- A member `n` of `S ⊆ ℕ` is primitive under divisibility when no proper
divisor of `n` also belongs to `S`. -/
def IsPrimitiveByDivisibility (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ Disjoint (n.properDivisors : Set ℕ) S

end Set
