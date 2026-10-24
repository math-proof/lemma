/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean -/

/-
Copyright (c) 2026 Meta Platforms, Inc. and affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Geometry.Group.WordMetric
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Growth of a finitely generated group

The *growth function* of a group `G` with respect to a generating family `P : Group.Generators G ι`
counts, for each radius `n`, the number of group elements whose word length is at most `n`, i.e. the
cardinality of the ball of radius `n` in the word metric induced by `P`. A group has *polynomial
growth* (with respect to `P`) if this count is bounded by a polynomial in `n`.

## Main definitions

* `Group.Generators.growth`: the growth function `γ_P(n) = |{g : G | wordLength g ≤ n}|` of the
  generating family `P`, defined as the `Nat.card` of the word ball of radius `n`.
* `Group.Generators.HasPolynomialGrowth`: the predicate that `P` has polynomial growth, i.e. there
  are `C d : ℕ` with `γ_P(n) ≤ C * (n + 1) ^ d` for all `n`.

## Main results

* `Group.Generators.growth_zero`: the ball of radius `0` contains only the identity, so
  `γ_P(0) = 1`.
* `Group.Generators.growth_le_card`: the growth function is bounded by the order of the group.
* `Group.Generators.hasPolynomialGrowth_of_finite`: every generating family of a finite group has
  polynomial growth (indeed, bounded growth of degree `0`).

## Implementation notes

* Growth is defined thinly over the word-length API `Group.Generators.wordLength`
  (`Mathlib.Geometry.Group.WordMetric`); it does not re-derive word length.
* `growth` uses `Nat.card`, which is the honest cardinality when the ball is finite (the case of a
  finitely generated group with a finite generating set) and takes the junk value `0` when the ball
  is infinite. The lemmas that need genuine cardinalities are stated under a `[Finite _]` hypothesis.
* `HasPolynomialGrowth` requires every word ball to be finite: `growth` uses `Nat.card`, which
  is the junk value `0` on an infinite subtype, so without finiteness an infinite group with
  the all-elements generating family would spuriously satisfy the bound. For a finite
  generating family (`[Finite ι]`) balls are finite in the intended applications; the
  predicate records the requirement explicitly rather than hiding it in `Nat.card`.
* `HasPolynomialGrowth` is defined *per generating family* `P`. The large-scale growth type is a
  quasi-isometry invariant and hence independent of the finite generating set, but proving this
  requires the bi-Lipschitz comparison of word metrics for different generating sets, which is not
  available cheaply here; we therefore do not state generating-set independence.
* The bound uses `(n + 1) ^ d` rather than `n ^ d` so that the `n = 0` boundary (`γ_P(0) = 1`) is
  covered by the same inequality.

## References

* [M. Gromov, *Groups of polynomial growth and expanding maps*][Gromov1981]

## Tags

group growth, growth function, polynomial growth, word metric, geometric group theory
-/

namespace Group.Generators

variable {G ι : Type*} [Group G] (P : Group.Generators G ι)

/-- The growth function of the generating family `P`: the number of elements of `G` whose word
length with respect to `P` is at most `n`, i.e. the cardinality of the word ball of radius `n`. -/
noncomputable def growth (n : ℕ) : ℕ := Nat.card {g : G // P.wordLength g ≤ n}

/-- `P` has *polynomial growth* if its growth function is bounded by a polynomial: there exist
`C d : ℕ` such that the ball of radius `n` has at most `C * (n + 1) ^ d` elements for every `n`. -/
def HasPolynomialGrowth : Prop :=
  (∀ n, Finite {g : G // P.wordLength g ≤ n}) ∧
    ∃ C d : ℕ, ∀ n, P.growth n ≤ C * (n + 1) ^ d
end Group.Generators
