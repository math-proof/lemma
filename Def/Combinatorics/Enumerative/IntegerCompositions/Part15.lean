/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.IntegerCompositions.Part9
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

/-- The filtered finset of bounded antidiagonals. -/
def boundedAntidiag (n k p : ℕ) : Finset (ℕ →₀ ℕ) :=
  (finsuppAntidiag (range k) n).filter (fun l => ∀ i ∈ range k, l i < p)

/-- Forward direction of the bijection: bounded antidiagonal → BoundedWeakComposition. -/
noncomputable def antidiagToBwc (n k p : ℕ) : 
    boundedAntidiag n k p → BoundedWeakComposition n k p := fun l => by
  have hl := l.prop
  simp only [boundedAntidiag, mem_filter, mem_finsuppAntidiag] at hl
  exact ⟨fun i => ⟨l.val i.val, hl.2 i.val (mem_range.mpr i.isLt)⟩, by
    have h := sum_range_eq_sum_fin k l.val
    simp only [← hl.1.1, h]⟩

/-- Backward direction of the bijection: BoundedWeakComposition → bounded antidiagonal. -/
noncomputable def bwcToAntidiag (n k p : ℕ) : 
    BoundedWeakComposition n k p → boundedAntidiag n k p := fun α => by
  let f : ℕ → ℕ := fun i => if h : i < k then (α.val ⟨i, h⟩).val else 0
  have hf : ∀ a, f a ≠ 0 → a ∈ range k := by
    intro a ha
    by_cases h : a < k
    · exact mem_range.mpr h
    · simp only [f, h, dite_false, ne_eq, not_true_eq_false] at ha
  let l := Finsupp.onFinset (range k) f hf
  refine ⟨l, ?_⟩
  simp only [boundedAntidiag, mem_filter, mem_finsuppAntidiag]
  refine ⟨⟨?_, Finsupp.support_onFinset_subset⟩, ?_⟩
  · have hsum : ∑ i ∈ range k, l i = ∑ i : Fin k, (α.val i).val := by
      simp only [l, Finsupp.onFinset_apply]
      trans ∑ i ∈ range k, (if h : i < k then (α.val ⟨i, h⟩).val else 0)
      · rfl
      rw [sum_dite_of_true (fun i hi => mem_range.mp hi)]
      rw [← Equiv.sum_comp (rangeEquivFin k)]
      apply sum_congr rfl
      intro i _
      simp [rangeEquivFin]
    rw [hsum, α.prop]
  · intro i hi
    simp only [l, Finsupp.onFinset_apply, f, mem_range.mp hi, dite_true]
    exact (α.val ⟨i, mem_range.mp hi⟩).isLt

end BoundedWeakComposition
end AlgebraicCombinatorics
