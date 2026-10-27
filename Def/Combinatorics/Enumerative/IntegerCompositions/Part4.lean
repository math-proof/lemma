/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.IntegerCompositions.Part2
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

/--
Equivalence between our `Composition.ofSize n` and Mathlib's `Composition n`.
This allows us to use Mathlib's `composition_card` theorem.
-/
def equivMathlib (n : ℕ) : Composition.ofSize n ≃ _root_.Composition n where
  toFun := fun ⟨α, hα⟩ => {
    blocks := toBlocks α
    blocks_pos := fun hi => by
      simp only [toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2
    blocks_sum := hα
  }
  invFun := fun c => ⟨ofBlocks c.blocks c.blocks_pos, by
    simp only [size_eq_sum_toBlocks, toBlocks_ofBlocks]
    exact c.blocks_sum⟩
  left_inv := fun ⟨α, hα⟩ => by
    simp only
    congr 1
    exact ofBlocks_toBlocks α
  right_inv := fun c => by
    simp only [_root_.Composition.ext_iff]
    exact toBlocks_ofBlocks c.blocks c.blocks_pos

/--
Equivalence between `Composition.ofSizeIntoParts n k` and the filtered set of Mathlib compositions
of `n` with length `k`.
-/
def equivMathlibFiltered (n k : ℕ) :
    Composition.ofSizeIntoParts n k ≃ {c : _root_.Composition n | c.length = k} where
  toFun := fun ⟨α, hα⟩ => ⟨{
    blocks := toBlocks α
    blocks_pos := fun hi => by
      simp only [toBlocks, List.mem_map] at hi
      obtain ⟨x, _, rfl⟩ := hi
      exact x.2
    blocks_sum := hα.1
  }, by
    simp only [Set.mem_ofPred_eq, _root_.Composition.length]
    rw [← len_eq_toBlocks_length]
    exact hα.2⟩
  invFun := fun ⟨c, hc⟩ => ⟨ofBlocks c.blocks c.blocks_pos, by
    simp only [size_eq_sum_toBlocks, toBlocks_ofBlocks]
    refine ⟨c.blocks_sum, ?_⟩
    simp only [len, ofBlocks, List.length_pmap]
    exact hc⟩
  left_inv := fun ⟨α, hα⟩ => by
    simp only
    congr 1
    exact ofBlocks_toBlocks α
  right_inv := fun ⟨c, hc⟩ => by
    simp only
    apply Subtype.ext
    simp only [_root_.Composition.ext_iff]
    exact toBlocks_ofBlocks c.blocks c.blocks_pos

end Composition
end AlgebraicCombinatorics
