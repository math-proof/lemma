/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Sidon.lean -/

/-
# Sidon sets
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace Set

/-- A set in an additive commutative monoid is Sidon when every equality of
two pairwise sums is trivial up to swapping the summands. Repeated summands
are included. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

end Set
