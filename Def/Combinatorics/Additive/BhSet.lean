import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Permutation
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

/-- Sum of the entries of a nonempty list, by folding `+` over the tail starting
from the head. The `l ≠ []` hypothesis rules out the empty list; it is ignored
by the computation, so it cannot affect the value
(see `sumNE_proof_irrel`). -/
def sumNE {G : Type*} [Add G] : (l : List G) → l ≠ [] → G
  | [], h => absurd rfl h
  | a :: t, _ => t.foldl (· + ·) a

end AdditiveCombinatorics
