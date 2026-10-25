import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Permutation
import Theorem.Combinatorics.Additive.BhSet
/-!
# `B_h`-sets

This file defines `B_h`-sets following Nathanson,
"`B_h`-sets of real and complex numbers" (<https://arxiv.org/abs/2502.21272v3>,
lines 197–203 and 230–235): a nonempty subset `A` of an additive commutative
semigroup, with `h` positive, such that any two sums of exactly `h`
(not necessarily distinct) elements of `A` that agree must use the same
summands up to permutation.

No zero or identity is assumed: the ambient type is only an
`AddCommSemigroup`, and sums of representations are computed with
`AdditiveCombinatorics.sumNE`, which folds `+` over the tail starting from
the head, so the theory applies to genuine semigroups.

## Main definitions

* `AdditiveCombinatorics.sumNE`: sum of a nonempty list.
* `AdditiveCombinatorics.sumNE_proof_irrel`: the nonemptiness proof does not
  affect the sum.
* `AdditiveCombinatorics.IsBhSet`: the `B_h`-set predicate.
-/


namespace AdditiveCombinatorics

/-- `IsBhSet A h` states that `A` is a `B_h`-set: `A` is nonempty, `h` is
positive, and any two length-`h` lists over `A` with equal nonempty sums are
permutations of each other. Repeated summands are allowed, since the
representatives are arbitrary lists. -/
def IsBhSet {G : Type*} [AddCommSemigroup G] (A : Set G) (h : ℕ) : Prop :=
  A.Nonempty ∧ 0 < h ∧
    ∀ (l₁ l₂ : List G),
      (∀ x ∈ l₁, x ∈ A) →
      (∀ x ∈ l₂, x ∈ A) →
      l₁.length = h →
      l₂.length = h →
      ∀ (e₁ : l₁ ≠ []) (e₂ : l₂ ≠ []),
        sumNE l₁ e₁ = sumNE l₂ e₂ → l₁.Perm l₂

end AdditiveCombinatorics
