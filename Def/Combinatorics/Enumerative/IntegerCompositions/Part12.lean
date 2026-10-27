/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.IntegerCompositions.Part7
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
Bijection between weak compositions of `n` into `k` parts and compositions of `n+k` into `k` parts.
Adding 1 to each entry of a weak composition gives a composition.

This is the key bijection used in the proof of Theorem thm.fps.comps.num-wcomps-n-k.
-/
def toComposition (n k : ℕ) :
    ofSizeIntoParts n k ≃ Composition.ofSizeIntoParts (n + k) k where
  toFun := fun ⟨lst, hsum, hlen⟩ =>
    ⟨lst.map (fun a => ⟨a + 1, Nat.succ_pos a⟩), by
      constructor
      · -- size = n + k
        simp only [Composition.size, List.map_map, Function.comp_def, PNat.mk_coe]
        rw [sum_map_add_one]
        simp only [size] at hsum
        simp only [len] at hlen
        rw [hsum, hlen]
      · -- len = k
        simp only [Composition.len, List.length_map]
        simp only [len] at hlen
        exact hlen⟩
  invFun := fun ⟨lst, hsum, hlen⟩ =>
    ⟨lst.map (fun b => b.val - 1), by
      constructor
      · -- size = n
        simp only [size]
        rw [sum_map_sub_one]
        simp only [Composition.size] at hsum
        simp only [Composition.len] at hlen
        rw [hsum, hlen]
        omega
      · -- len = k
        simp only [len, List.length_map]
        simp only [Composition.len] at hlen
        exact hlen⟩
  left_inv := fun ⟨lst, hsum, hlen⟩ => by
    apply Subtype.ext
    simp only [List.map_map, Function.comp_def, PNat.mk_coe, Nat.add_sub_cancel]
    exact List.map_id' lst
  right_inv := fun ⟨lst, hsum, hlen⟩ => by
    apply Subtype.ext
    simp only [List.map_map, Function.comp_def]
    have h : ∀ a : ℕ+, (⟨a.val - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = a := by
      intro a
      simp only [Nat.sub_add_cancel (a.pos)]
      rfl
    simp only [h]
    exact List.map_id lst

end WeakComposition

/-! ### Bounded Weak Compositions -/


/--
A weak composition of `n` into `k` parts with entries bounded by `p`
(i.e., each entry is in `{0, 1, ..., p-1}`).

This is used in Theorem thm.fps.comps.num-wpcomps-n-k.
-/
def BoundedWeakComposition (n k p : ℕ) : Type :=
  { α : Fin k → Fin p // (∑ i, (α i).val) = n }

end AlgebraicCombinatorics
