import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Permutation
import Def.Combinatorics.Additive.BhSet
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

/-- `sumNE` does not depend on the nonemptiness proof, so that proof cannot
alter the semantics of the sum. -/
theorem sumNE_proof_irrel {G : Type*} [Add G] (l : List G) (e₁ e₂ : l ≠ []) :
    sumNE l e₁ = sumNE l e₂ := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

end AdditiveCombinatorics
