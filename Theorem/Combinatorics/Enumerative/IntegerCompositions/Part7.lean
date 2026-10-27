/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Instance.Combinatorics.Enumerative.IntegerCompositions.Part7
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

/-- Helper lemma: sum of list after adding 1 to each element. -/
theorem sum_map_add_one (lst : List ℕ) : 
    (lst.map (fun a => a + 1)).sum = lst.sum + lst.length := by
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih]
    ring

/-- Helper lemma: sum of PNat values is at least the length. -/
theorem pnat_list_sum_ge_length (lst : List ℕ+) : 
    (lst.map (·.val)).sum ≥ lst.length := by
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have : 1 ≤ h.val := h.pos
    omega

/-- Helper lemma: sum of list after subtracting 1 from each PNat element. -/
theorem sum_map_sub_one (lst : List ℕ+) : 
    (lst.map (fun b : ℕ+ => b.val - 1)).sum = (lst.map (·.val)).sum - lst.length := by
  induction lst with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hpos : 1 ≤ h.val := h.pos
    have ht_sum_ge : (t.map (·.val)).sum ≥ t.length := pnat_list_sum_ge_length t
    omega

end WeakComposition
end AlgebraicCombinatorics
