/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
/-!
# More Subtractive Methods

This file formalizes Section `sec.cancel.moresub` on more subtractive methods
in combinatorics, focusing on the technique of summing with varying signs to
achieve cancellation.

## Main definitions

* `IsAllEven`: An n-tuple `x : Fin n → Fin d` is "all-even" if each element
  of `Fin d` occurs an even number of times in the tuple.
* `signProduct`: The product `e_{x_1} * e_{x_2} * ... * e_{x_n}` for a sign tuple `e`
  and index tuple `x`.
* `signSum`: The sum of entries of a sign tuple, as an integer.
* `allEvenTuples`: The set of all-even tuples in `(Fin n → Fin d)`.
* `signTupleEquivSubset`: Equivalence between sign tuples and subsets of `[d]`.

## Main results

* `sum_signSum_pow_eq_sum_signProduct`: Sum interchange identity (Lemma `lem.cancel.all-even.l1`).
* `sum_signProduct_not_allEven`: If an n-tuple is not all-even, then the sum
  `∑_{e ∈ {1,-1}^d} ∏_i e_{x_i}` equals 0 (Lemma `lem.cancel.all-even.l2(a)`).
* `sum_signProduct_allEven`: If an n-tuple is all-even, then the sum
  `∑_{e ∈ {1,-1}^d} ∏_i e_{x_i}` equals 2^d (Lemma `lem.cancel.all-even.l2(b)`).
* `allEven_count_formula`: The number of all-even n-tuples in `[d]^n` equals
  `(1/2^d) ∑_{k=0}^d C(d,k) (d-2k)^n` (Theorem `thm.cancel.all-even`).
* `sum_choose_pow_dvd_pow_two`: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is divisible by `2^d`.
* `sum_choose_pow_nonneg`: The sum `∑_{k=0}^d C(d,k) (d-2k)^n` is nonnegative.

## References

* Source: `AlgebraicCombinatorics/tex/SignedCounting/SubtractiveMethods.tex`
-/


open Finset BigOperators

namespace AlgebraicCombinatorics.SubtractiveMethods
/-! ### The all-even property

An n-tuple `(x₁, x₂, ..., xₙ) ∈ [d]ⁿ` is called "all-even" if each element
of `[d]` occurs an even number of times in the tuple.
-/


/-- An n-tuple `x : Fin n → Fin d` is "all-even" if each element of `Fin d`
occurs an even number of times. For example, the 4-tuple `(1,4,4,1)` is all-even
since 1 appears twice and 4 appears twice.

Label: Definition from Theorem `thm.cancel.all-even` -/
def IsAllEven {n d : ℕ} (x : Fin n → Fin d) : Prop :=
  ∀ k : Fin d, Even ((univ.filter fun i => x i = k).card)

/-- The multiplicity of element `k` in tuple `x` -/
def multiplicity {n d : ℕ} (x : Fin n → Fin d) (k : Fin d) : ℕ :=
  (univ.filter fun i => x i = k).card

instance {n d : ℕ} (x : Fin n → Fin d) : Decidable (IsAllEven x) :=
  inferInstanceAs (Decidable (∀ k : Fin d, Even ((univ.filter fun i => x i = k).card)))
/-! ### Sign tuples

We represent sign tuples as functions `e : Fin d → ZMod 2`, where
`0` represents `+1` and `1` represents `-1`. This gives us a natural
finite type structure. We then convert to ℤ when needed.
-/


/-- Convert a ZMod 2 value to a sign: 0 ↦ 1, 1 ↦ -1 -/
def toSign (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

/-- The product `e_{x_1} * e_{x_2} * ... * e_{x_n}` for a sign tuple `e` and
index tuple `x` -/
def signProduct {n d : ℕ} (e : Fin d → ZMod 2) (x : Fin n → Fin d) : ℤ :=
  ∏ i : Fin n, toSign (e (x i))
/-! ### Helper lemmas about toSign and powers -/
/-! ### Lemma `lem.cancel.all-even.l1`: Sum interchange

This lemma establishes that:
```
∑_{e ∈ {1,-1}^d} (e_1 + e_2 + ... + e_d)^n =
  ∑_{x ∈ [d]^n} ∑_{e ∈ {1,-1}^d} e_{x_1} * e_{x_2} * ... * e_{x_n}
```
-/


/-- The sum of entries of a sign tuple, as an integer -/
def signSum {d : ℕ} (e : Fin d → ZMod 2) : ℤ :=
  ∑ k : Fin d, toSign (e k)
/-! ### Lemma `lem.cancel.all-even.l2`: Computing the inner sums

Part (a): If the tuple is not all-even, the sum of sign products is 0.
Part (b): If the tuple is all-even, the sum of sign products is 2^d.
-/
/-! #### The involution for cancellation

We define an involution on sign tuples that flips the sign at position `k`.
This is used to show cancellation when the tuple has odd multiplicity at `k`.
-/


/-- The involution that flips the k-th sign: if `e_k = +1`, make it `-1`, and vice versa -/
def flipSign {d : ℕ} (k : Fin d) (e : Fin d → ZMod 2) : Fin d → ZMod 2 :=
  Function.update e k (e k + 1)
/-! ### Theorem `thm.cancel.all-even`: The counting formula

The number of all-even n-tuples in `[d]^n` equals
`(1/2^d) ∑_{k=0}^d C(d,k) (d-2k)^n`.
-/


/-- The set of all-even tuples in `(Fin n → Fin d)` -/
def allEvenTuples (n d : ℕ) : Finset (Fin n → Fin d) :=
  univ.filter IsAllEven

/-- Bijection between sign tuples and subsets of `[d]`:
A sign tuple `(e_1, ..., e_d) ∈ {1,-1}^d` corresponds to the set
`{i ∈ [d] | e_i = -1}` of positions with -1. -/
def signTupleToSubset {d : ℕ} (e : Fin d → ZMod 2) : Finset (Fin d) :=
  univ.filter fun k => e k = 1
/-! ### Bijection between sign tuples and subsets -/


/-- Inverse of signTupleToSubset: given a subset S, produce the sign tuple
where position k has value 1 (representing -1) iff k ∈ S -/
def subsetToSignTuple {d : ℕ} (S : Finset (Fin d)) : Fin d → ZMod 2 :=
  fun k => if k ∈ S then 1 else 0

theorem signTupleToSubset_subsetToSignTuple {d : ℕ} (S : Finset (Fin d)) :
    signTupleToSubset (subsetToSignTuple S) = S := by
  ext k
  simp [signTupleToSubset, subsetToSignTuple]

theorem subsetToSignTuple_signTupleToSubset {d : ℕ} (e : Fin d → ZMod 2) :
    subsetToSignTuple (signTupleToSubset e) = e := by
  ext k
  simp only [subsetToSignTuple, signTupleToSubset, mem_filter, mem_univ, true_and]
  have hlt : (e k).val < 2 := (e k).isLt
  interval_cases h : (e k).val
  · have he : e k = 0 := Fin.ext h
    simp [he]
  · have he : e k = 1 := Fin.ext h
    simp [he]

/-- Equivalence between sign tuples and subsets of `[d]` -/
def signTupleEquivSubset (d : ℕ) : (Fin d → ZMod 2) ≃ Finset (Fin d) where
  toFun := signTupleToSubset
  invFun := subsetToSignTuple
  left_inv := subsetToSignTuple_signTupleToSubset
  right_inv := signTupleToSubset_subsetToSignTuple

end AlgebraicCombinatorics.SubtractiveMethods
