/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.IntegerCompositions.Part6
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

/--
The two representations (list-based and function-based) are equivalent.
The forward direction converts a list `[a₀, a₁, ..., aₖ₋₁]` to the function `i ↦ aᵢ`.
The backward direction converts a function `f : Fin k → ℕ` to the list `[f(0), f(1), ..., f(k-1)]`.
-/
def ofSizeIntoParts_equiv (n k : ℕ) : ofSizeIntoParts n k ≃ ofSizeIntoParts' n k where
  toFun := fun ⟨α, hsize, hlen⟩ => ⟨toFun α k hlen, by
    simp only [toFun, size] at *
    have h1 : (∑ i : Fin k, α.get (Fin.cast hlen.symm i)) = ∑ i : Fin α.length, α.get i := by
      apply Finset.sum_equiv (Fin.castOrderIso hlen.symm).toEquiv
      · intro i
        exact iff_of_true (Finset.mem_univ i) (Finset.mem_univ _)
      · intro i _
        rfl
    rw [h1, ← list_sum_eq_finset_sum, hsize]⟩
  invFun := fun ⟨f, hsum⟩ => ⟨ofFun f, by simp [size, ofFun_sum, hsum], by simp [len, ofFun_length]⟩
  left_inv := fun ⟨α, hsize, hlen⟩ => by
    simp only
    apply Subtype.ext
    exact ofFun_toFun α k hlen
  right_inv := fun ⟨f, hsum⟩ => by
    simp only
    apply Subtype.ext
    exact toFun_ofFun f

end WeakComposition
end AlgebraicCombinatorics
