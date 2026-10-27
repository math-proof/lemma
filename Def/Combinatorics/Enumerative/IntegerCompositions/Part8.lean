/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.IntegerCompositions.Part4
open Finset Nat BigOperators
set_option allowUnsafeReducibility true
attribute [local reducible] PNat

/-!
# Integer Compositions

This file formalizes integer compositions and weak compositions, following
Section sec.fps.intcomps of the source text.

## Main definitions

* `Composition` - A composition as a `List ℕ+` (tuple of positive integers)
* `Composition.append` - Concatenation of two compositions
* `Composition.ofSize n` - The subtype of compositions with size `n`
* `Composition.ofSizeIntoParts n k` - The subtype of compositions with size `n` and length `k`
* `WeakComposition` - A weak composition as a `List ℕ` (tuple of nonnegative integers)
* `WeakComposition.ofSizeIntoParts n k` - Weak compositions of `n` into `k` parts
* `BoundedWeakComposition n k p` - Weak compositions with entries in `{0, 1, ..., p-1}`

## Main results

* `Composition.card_ofSizeIntoParts_pos` - The number of compositions of `n` into `k` parts
  is `Nat.choose (n-1) (k-1)` for `n > 0` and `k > 0` (Theorem thm.fps.comps.num-comps-n-k)
* `Composition.card_ofSizeIntoParts_zero` - The number of compositions of `0` into `k` parts
  is `1` if `k = 0`, else `0`
* `Composition.card_ofSizeIntoParts_k_zero` - The number of compositions of `n > 0` into
  `0` parts is `0`
* `Composition.card_ofSize` - The number of compositions of `n` is `2^(n-1)` for `n > 0`
  (Theorem thm.fps.comps.num-comps-n)
* `WeakComposition.card_ofSizeIntoParts` - The number of weak compositions of `n` into `k` parts
  is `Nat.choose (n+k-1) n` (Theorem thm.fps.comps.num-wcomps-n-k)
* `BoundedWeakComposition.card` - The number of weak compositions with bounded entries
  (Theorem thm.fps.comps.num-wpcomps-n-k)
* `binom_sum_identity` - An identity involving binomial coefficients
  (Proposition prop.fps.comps.num-w2comps-n-k-id)

## Implementation notes

This file defines `Composition` as `List ℕ+`, which is an alternative representation to
Mathlib's `Mathlib.Combinatorics.Enumerative.Composition` which uses `Composition n` as a
structure with `blocks : List ℕ` and proofs of positivity and sum. Both representations
are equivalent; we use `List ℕ+` here to follow the source text's presentation more directly.

## References

See the source LaTeX file `AlgebraicCombinatorics/tex/FPS/IntegerCompositions.tex`
-/


namespace AlgebraicCombinatorics

namespace WeakComposition

namespace ofSizeIntoParts'

/-- Bijection from `Sym (Fin k) n` to `ofSizeIntoParts' n k`. -/
def fromSym (n k : ℕ) : Sym (Fin k) n → ofSizeIntoParts' n k := fun s =>
  ⟨fun i => Multiset.count i s.val, by rw [sum_count_eq_card]; exact s.prop⟩

/-- Bijection from `ofSizeIntoParts' n k` to `Sym (Fin k) n`. -/
def toSym (n k : ℕ) : ofSizeIntoParts' n k → Sym (Fin k) n := fun ⟨f, hf⟩ =>
  ⟨∑ i : Fin k, Multiset.replicate (f i) i, by
    simp only [Multiset.card_sum, Multiset.card_replicate]
    exact hf⟩

end ofSizeIntoParts'
end WeakComposition
end AlgebraicCombinatorics
