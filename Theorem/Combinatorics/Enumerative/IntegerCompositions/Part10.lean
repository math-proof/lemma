/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.Combinatorics.Enumerative.IntegerCompositions.Part15
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

namespace BoundedWeakComposition

/-- Left inverse property of the bijection. -/
theorem bwc_left_inv (n k p : ℕ) (α : BoundedWeakComposition n k p) : 
    antidiagToBwc n k p (bwcToAntidiag n k p α) = α := by
  simp only [antidiagToBwc, bwcToAntidiag]
  congr 1
  ext i
  simp only [Finsupp.onFinset_apply, i.isLt, dite_true]

/-- Right inverse property of the bijection. -/
theorem bwc_right_inv (n k p : ℕ) (l : boundedAntidiag n k p) : 
    bwcToAntidiag n k p (antidiagToBwc n k p l) = l := by
  have hl := l.prop
  simp only [boundedAntidiag, mem_filter, mem_finsuppAntidiag] at hl
  simp only [antidiagToBwc, bwcToAntidiag]
  congr 1
  ext i
  simp only [Finsupp.onFinset_apply]
  by_cases hi : i < k
  · simp [hi]
  · have : l.val i = 0 := by
      by_contra h
      have h1 : i ∈ l.val.support := Finsupp.mem_support_iff.mpr h
      have h2 : i ∈ range k := hl.1.2 h1
      exact hi (mem_range.mp h2)
    simp [hi, this]

end BoundedWeakComposition
end AlgebraicCombinatorics
