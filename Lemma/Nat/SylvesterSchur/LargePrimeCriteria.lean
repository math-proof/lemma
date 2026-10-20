import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur.LargePrimeCriteria
open scoped BigOperators
open Finset Nat
open Nat.SylvesterSchur


/--
[exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_layers_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_layers_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hbound : r ! * (∏ j ∈ Finset.range (Nat.log 2 N), if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_layers_lt_lower_pow hN hrN hbound

/--
[exists_large_prime_dvd_choose_of_factorial_mul_prod_primorial_nthRoot_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_prod_primorial_nthRoot_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hbound : r ! * (∏ j ∈ Finset.range (Nat.log 2 N), primorial (Nat.nthRoot (j + 1) N)) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_prod_primorial_nthRoot_lt_lower_pow hN hrN hbound

/--
[exists_large_prime_dvd_choose_of_mul_top_pow_sqrt_mul_primorial_lt_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_mul_top_pow_sqrt_mul_primorial_lt_four_pow_eq
  {N r : ℕ}
-- given
  (hr : 4 ≤ r)
  (hN : 2 * r ≤ N)
  (hbound : r * (N ^ (Nat.sqrt N + 1) * primorial r) < 4 ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_mul_top_pow_sqrt_mul_primorial_lt_four_pow hr hN hbound

/--
[exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hbound : r ! * (N ^ (Nat.sqrt N + 1) * primorial r) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_lower_pow hN hrN hbound

/--
[exists_large_prime_dvd_choose_of_factorial_mul_top_pow_primeCounting_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_top_pow_primeCounting_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hbound : r ! * N ^ Nat.primeCounting r < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_top_pow_primeCounting_lt_lower_pow hN hrN hbound

/--
[exists_large_prime_dvd_choose_of_factorial_mul_top_pow_half_add_one_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_top_pow_half_add_one_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hbound : r ! * N ^ (r / 2 + 1) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_top_pow_half_add_one_lt_lower_pow hN hrN hbound

/--
[exists_large_prime_dvd_choose_of_factorial_mul_top_pow_three_mul_div_eight_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_top_pow_three_mul_div_eight_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hr : 38 ≤ r)
  (hrN : r ≤ N)
  (hbound : r ! * N ^ (3 * r / 8) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_top_pow_three_mul_div_eight_lt_lower_pow hN hr hrN hbound

/--
[exists_large_prime_dvd_choose_of_self_pow_mul_top_pow_three_mul_div_eight_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_self_pow_mul_top_pow_three_mul_div_eight_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hr : 38 ≤ r)
  (hrN : r ≤ N)
  (hbound : r ^ r * N ^ (3 * r / 8) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_self_pow_mul_top_pow_three_mul_div_eight_lt_lower_pow hN hr hrN hbound

/--
[exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sub_one_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/LargePrimeCriteria.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sub_one_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hr : 2 ≤ r)
  (hrN : r ≤ N)
  (hbound : r ! * N ^ (r - 1) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_top_pow_sub_one_lt_lower_pow hN hr hrN hbound


-- created on 2026-10-20
