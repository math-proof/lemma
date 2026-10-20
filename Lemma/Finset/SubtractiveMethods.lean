import Mathlib
import sympy.Basic
import sympy.concrete.SubtractiveMethods
open scoped BigOperators
open AlgebraicCombinatorics.SubtractiveMethods


/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma isAllEven_iff_multiplicity
-- given
  {n d : ℕ}
  (x : Fin n → Fin d) :
-- imply
  IsAllEven x ↔ ∀ k : Fin d, Even (multiplicity x k) := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.isAllEven_iff_multiplicity

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma toSign_zero :
-- imply
  toSign 0 = 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_zero

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma toSign_one :
-- imply
  toSign 1 = -1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_one

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma toSign_sq
-- given
  (b : ZMod 2) :
-- imply
  toSign b ^ 2 = 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_sq

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma toSign_pow_even
-- given
  (b : ZMod 2)
  (m : ℕ)
  (hm : Even m) :
-- imply
  toSign b ^ m = 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_pow_even b m hm

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma toSign_pow_odd
-- given
  (b : ZMod 2)
  (m : ℕ)
  (hm : Odd m) :
-- imply
  toSign b ^ m = toSign b := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_pow_odd b m hm

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma toSign_add_one
-- given
  (b : ZMod 2) :
-- imply
  toSign (b + 1) = -toSign b := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.toSign_add_one

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma signProduct_eq_prod_pow
-- given
  {n d : ℕ}
  (e : Fin d → ZMod 2)
  (x : Fin n → Fin d) :
-- imply
  signProduct e x = ∏ k : Fin d, (toSign (e k)) ^ (multiplicity x k) := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signProduct_eq_prod_pow

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_signSum_pow_eq_sum_signProduct
-- given
  (n d : ℕ) :
-- imply
  ∑ e : Fin d → ZMod 2, (signSum e) ^ n =
    ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signSum_pow_eq_sum_signProduct

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma flipSign_involutive
-- given
  {d : ℕ}
  (k : Fin d) :
-- imply
  Function.Involutive (flipSign k) := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_involutive

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma flipSign_ne
-- given
  {d : ℕ}
  (k : Fin d)
  (e : Fin d → ZMod 2) :
-- imply
  flipSign k e ≠ e := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_ne

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma flipSign_self
-- given
  {d : ℕ}
  (k : Fin d)
  (e : Fin d → ZMod 2) :
-- imply
  (flipSign k e) k = e k + 1 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_self

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma flipSign_ne_self
-- given
  {d : ℕ}
  (k j : Fin d)
  (h : j ≠ k)
  (e : Fin d → ZMod 2) :
-- imply
  (flipSign k e) j = e j := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.flipSign_ne_self k j e h

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma signProduct_flipSign
-- given
  {n d : ℕ}
  (e : Fin d → ZMod 2)
  (x : Fin n → Fin d)
  (k : Fin d)
  (hk : Odd (multiplicity x k)) :
-- imply
  signProduct (flipSign k e) x = -signProduct e x := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signProduct_flipSign e x k hk

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_signProduct_not_allEven
-- given
  {n d : ℕ}
  (x : Fin n → Fin d)
  (hx : ¬IsAllEven x) :
-- imply
  ∑ e : Fin d → ZMod 2, signProduct e x = 0 := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signProduct_not_allEven x hx

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_signProduct_allEven
-- given
  {n d : ℕ}
  (x : Fin n → Fin d)
  (hx : IsAllEven x) :
-- imply
  ∑ e : Fin d → ZMod 2, signProduct e x = 2 ^ d := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signProduct_allEven x hx

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma signSum_eq_card
-- given
  {d : ℕ}
  (e : Fin d → ZMod 2) :
-- imply
  signSum e = d - 2 * (signTupleToSubset e).card := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signSum_eq_card

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma signTupleToSubset_subsetToSignTuple
-- given
  {d : ℕ}
  (S : Finset (Fin d)) :
-- imply
  signTupleToSubset (subsetToSignTuple S) = S := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signTupleToSubset_subsetToSignTuple

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma subsetToSignTuple_signTupleToSubset
-- given
  {d : ℕ}
  (e : Fin d → ZMod 2) :
-- imply
  subsetToSignTuple (signTupleToSubset e) = e := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.subsetToSignTuple_signTupleToSubset

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma signSum_subsetToSignTuple
-- given
  {d : ℕ}
  (S : Finset (Fin d)) :
-- imply
  signSum (subsetToSignTuple S) = d - 2 * S.card := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.signSum_subsetToSignTuple

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_signProduct_eq_allEven_count
-- given
  (n d : ℕ) :
-- imply
  ∑ x : Fin n → Fin d, ∑ e : Fin d → ZMod 2, signProduct e x =
    (allEvenTuples n d).card * 2 ^ d := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signProduct_eq_allEven_count

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_signSum_pow_eq_sum_subset
-- given
  (n d : ℕ) :
-- imply
  ∑ e : Fin d → ZMod 2, (signSum e) ^ n =
    ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_signSum_pow_eq_sum_subset

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_subset_eq_sum_choose
-- given
  (n d : ℕ) :
-- imply
  ∑ S : Finset (Fin d), (d - 2 * S.card : ℤ) ^ n =
    ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_subset_eq_sum_choose

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma allEven_count_formula
-- given
  (n d : ℕ) :
-- imply
  ((allEvenTuples n d).card : ℤ) * 2 ^ d =
    ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.allEven_count_formula

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_choose_pow_dvd_pow_two
-- given
  (n d : ℕ) :
-- imply
  (2 ^ d : ℤ) ∣ ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_choose_pow_dvd_pow_two

/--
[SubtractiveMethods](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/SignedCounting/SubtractiveMethods.lean)
-/
@[path]
private lemma sum_choose_pow_nonneg
-- given
  (n d : ℕ) :
-- imply
  0 ≤ ∑ k ∈ Finset.range (d + 1), d.choose k * (d - 2 * k : ℤ) ^ n := by
-- proof
  apply AlgebraicCombinatorics.SubtractiveMethods.sum_choose_pow_nonneg


-- created on 2026-10-20
