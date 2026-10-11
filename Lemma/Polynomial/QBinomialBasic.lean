import Mathlib
import sympy.Basic
import sympy.combinatorics.qbinomial.QBinomialBasic
open Finset
open Nat
open scoped BigOperators


/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_int_eq_geom_sum_eq
-- given
  {R : Type*} [CommRing R] (n : ℕ) (q : R) :
-- imply
  (1 - q) * AlgebraicCombinatorics.qInt n q = 1 - q ^ n := by
-- proof
  apply AlgebraicCombinatorics.qInt_eq_geom_sum n q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_factorial_one_eq
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) :
-- imply
  AlgebraicCombinatorics.qFactorial n (1 : R) = n ! := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_one_eq n

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_sum_increasing_tuples_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    ∑ f ∈ AlgebraicCombinatorics.monotoneFunctions k (n - k),
      q ^ (∑ i, (f i).val) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_sum_increasing_tuples n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_partition_gf_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    ∑ m ∈ range (k * (n - k) + 1),
      (AlgebraicCombinatorics.partitionsInBox m k (n - k)).card • q ^ m := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_partition_gf n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_one_eq_binomial_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) :
-- imply
  AlgebraicCombinatorics.qBinomial n k (1 : R) = Nat.choose n k := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_one_eq_binomial n k

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_zero_of_lt_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : n < k) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q = 0 := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_zero_of_lt n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_n_zero_eq
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n 0 q = 1 := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_n_zero n q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_n_n_eq
-- given
  {R : Type*} [CommSemiring R] (n : ℕ) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n n q = 1 := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_n_n n q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_rec_left_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    q ^ (n - k) * AlgebraicCombinatorics.qBinomial (n - 1) (k - 1) q +
      AlgebraicCombinatorics.qBinomial (n - 1) k q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_rec_left n hn k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_rec_right_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    AlgebraicCombinatorics.qBinomial (n - 1) (k - 1) q +
      q ^ k * AlgebraicCombinatorics.qBinomial (n - 1) k q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_rec_right n hn k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_quot_formula_eq
-- given
  {R : Type*} [CommRing R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  (∏ i ∈ range k, (1 - q ^ (i + 1))) * AlgebraicCombinatorics.qBinomial n k q =
    ∏ i ∈ range k, (1 - q ^ (n - i)) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_quot_formula n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_prod_quot_eq
-- given
  {R : Type*} [Field R] (n k : ℕ) (q : R) (hk : k ≤ n)
  (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    ∏ i ∈ range k, (1 - q ^ (n - i)) / (1 - q ^ (i + 1)) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_prod_quot n k hk q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_q_int_prod_quot_eq
-- given
  {R : Type*} [Field R] (n k : ℕ) (q : R) (hk : k ≤ n)
  (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    (∏ i ∈ range k, AlgebraicCombinatorics.qInt (n - i) q) /
      AlgebraicCombinatorics.qFactorial k q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_qInt_prod_quot n k hk q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_eq_q_factorial_quot_eq
-- given
  {R : Type*} [Field R] (n k : ℕ) (q : R) (hk : k ≤ n)
  (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q =
    AlgebraicCombinatorics.qFactorial n q /
      (AlgebraicCombinatorics.qFactorial k q *
        AlgebraicCombinatorics.qFactorial (n - k) q) := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_eq_qFactorial_quot n k hk q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_binomial_symm_eq
-- given
  {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≤ n) (q : R) :
-- imply
  AlgebraicCombinatorics.qBinomial n k q = AlgebraicCombinatorics.qBinomial n (n - k) q := by
-- proof
  apply AlgebraicCombinatorics.qBinomial_symm n k hk q

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma card_monotone_functions_sum_eq
-- given
  (k m s : ℕ) (hs : s ≤ k * m) :
-- imply
  ((AlgebraicCombinatorics.monotoneFunctions k m).filter fun f =>
      ∑ i, (f i).val = s).card =
    (AlgebraicCombinatorics.partitionsInBox s k m).card := by
-- proof
  apply AlgebraicCombinatorics.card_monotoneFunctions_sum_eq k m s hs

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma card_monotone_functions_eq_choose_eq
-- given
  (k ℓ : ℕ) :
-- imply
  (AlgebraicCombinatorics.monotoneFunctions k ℓ).card = Nat.choose (k + ℓ) k := by
-- proof
  apply AlgebraicCombinatorics.card_monotoneFunctions_eq_choose k ℓ

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma card_partitions_with_parts_and_largest_eq
-- given
  (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
-- imply
  (AlgebraicCombinatorics.monotoneFunctions (k - 1) (ℓ - 1)).card =
    Nat.choose (k + ℓ - 2) (k - 1) := by
-- proof
  apply AlgebraicCombinatorics.card_partitions_with_parts_and_largest k ℓ hk hℓ

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_int_ne_zero_is
-- given
  {R : Type*} [Field R] (n : ℕ) (q : R) (hq : q ^ n ≠ 1) :
-- imply
  AlgebraicCombinatorics.qInt n q ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.qInt_ne_zero n q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma q_factorial_ne_zero_is
-- given
  {R : Type*} [Field R] (n : ℕ) (q : R)
  (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) :
-- imply
  AlgebraicCombinatorics.qFactorial n q ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.qFactorial_ne_zero n q hq

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma transpose_monotone_involutive_eq
-- given
  (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f) :
-- imply
  AlgebraicCombinatorics.transposeMonotone m k
    (AlgebraicCombinatorics.transposeMonotone k m f) = f := by
-- proof
  apply AlgebraicCombinatorics.transposeMonotone_involutive k m f hf

/-- [QBinomialBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/QBinomialBasic.lean) -/
@[path]
private lemma sum_transpose_monotone_eq
-- given
  (k m : ℕ) (f : Fin k → Fin (m + 1)) :
-- imply
  ∑ j : Fin m, (AlgebraicCombinatorics.transposeMonotone k m f j).val =
    ∑ i : Fin k, (f i).val := by
-- proof
  apply AlgebraicCombinatorics.sum_transposeMonotone k m f


-- created on 2026-10-11
