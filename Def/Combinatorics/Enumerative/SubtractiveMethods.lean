/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
open Finset BigOperators

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

end AlgebraicCombinatorics.SubtractiveMethods
