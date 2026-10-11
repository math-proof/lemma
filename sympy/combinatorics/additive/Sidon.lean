/-
# Sidon sets
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

namespace Set

/-- A set in an additive commutative monoid is Sidon when every equality of
two pairwise sums is trivial up to swapping the summands. Repeated summands
are included. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

end Set
