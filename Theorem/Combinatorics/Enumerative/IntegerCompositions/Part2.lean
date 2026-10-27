/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Def.Combinatorics.Enumerative.IntegerCompositions.Part3
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

namespace Composition

theorem toBlocks_ofBlocks (blocks : List ℕ) (hpos : ∀ {i}, i ∈ blocks → 0 < i) :
    toBlocks (ofBlocks blocks hpos) = blocks := by
  simp only [toBlocks, ofBlocks]
  induction blocks with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.pmap_cons, List.map_cons]
    congr 1
    exact ih (fun hi => hpos (List.mem_cons_of_mem x hi))

theorem ofBlocks_toBlocks (α : Composition) :
    ofBlocks (toBlocks α) (fun hi => by
      simp only [toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2) = α := by
  simp only [toBlocks, ofBlocks]
  induction α with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.pmap_cons]
    rw [List.cons.injEq]
    exact ⟨rfl, ih⟩

theorem size_eq_sum_toBlocks (α : Composition) : α.size = (toBlocks α).sum := rfl

theorem len_eq_toBlocks_length (α : Composition) : α.len = (toBlocks α).length := by
  simp [len, toBlocks]

end Composition
end AlgebraicCombinatorics
