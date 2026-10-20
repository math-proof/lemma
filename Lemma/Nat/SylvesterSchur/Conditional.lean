import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur.Conditional
open scoped BigOperators
open Finset Nat
open Nat.SylvesterSchur


/--
[consecutive_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_two_eq
  {k : ℕ}
-- given
  (hk : 2 < k) :
-- imply
  ∃ i : ℕ, i < 2 ∧ ∃ p : ℕ, p.Prime ∧ 2 < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_two hk

/--
[consecutive_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_three_eq
  {k : ℕ}
-- given
  (hk : 3 < k) :
-- imply
  ∃ i : ℕ, i < 3 ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_three hk

/--
[consecutive_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_four_eq
  {k : ℕ}
-- given
  (hk : 4 < k) :
-- imply
  ∃ i : ℕ, i < 4 ∧ ∃ p : ℕ, p.Prime ∧ 4 < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_four hk

/--
[consecutive_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_five_eq
  {k : ℕ}
-- given
  (hk : 5 < k) :
-- imply
  ∃ i : ℕ, i < 5 ∧ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_five hk

/--
[consecutive_six](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_six_eq
  {k : ℕ}
-- given
  (hk : 6 < k) :
-- imply
  ∃ i : ℕ, i < 6 ∧ ∃ p : ℕ, p.Prime ∧ 6 < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_six hk

/--
[consecutive_of_factorial_mul_top_pow_primeCounting_lt_start_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_of_factorial_mul_top_pow_primeCounting_lt_start_pow_eq
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * (k + n - 1) ^ Nat.primeCounting n < k ^ n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_factorial_mul_top_pow_primeCounting_lt_start_pow hn hk hbound

/--
[consecutive_of_factorial_mul_top_pow_half_add_one_lt_start_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_of_factorial_mul_top_pow_half_add_one_lt_start_pow_eq
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * (k + n - 1) ^ (n / 2 + 1) < k ^ n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_factorial_mul_top_pow_half_add_one_lt_start_pow hn hk hbound

/--
[consecutive_of_quadratic_start](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_of_quadratic_start_eq
  {n k : ℕ}
-- given
  (hn : 38 ≤ n)
  (hkquad : n ^ 2 < k) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_quadratic_start hn hkquad

/--
[consecutive_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_start_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_start_pow_eq
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * ((k + n - 1) ^ (Nat.sqrt (k + n - 1) + 1) * primorial n) < k ^ n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_start_pow hn hk hbound

/--
[consecutive_of_factorial_mul_prod_erdos_layers_lt_start_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_of_factorial_mul_prod_erdos_layers_lt_start_pow_eq
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)), if j = 0 then primorial n else primorial (Nat.nthRoot (j + 1) (k + n - 1))) < k ^ n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_factorial_mul_prod_erdos_layers_lt_start_pow hn hk hbound

/--
[consecutive_of_factorial_mul_prod_erdos_div_three_layers_lt_start_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_of_factorial_mul_prod_erdos_div_three_layers_lt_start_pow_eq
  {n k : ℕ}
-- given
  (hk : n < k)
  (hN6 : 6 ≤ k + n - 1)
  (hbound : n ! * (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)), if j = 0 then primorial ((k + n - 1) / 3) else primorial (Nat.nthRoot (j + 1) (k + n - 1))) < k ^ n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_factorial_mul_prod_erdos_div_three_layers_lt_start_pow hk hN6 hbound

/--
[consecutive_of_large_start](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Conditional.lean)
-/
@[path]
private lemma consecutive_of_large_start_eq
  {n k : ℕ}
-- given
  (hn : 2 ≤ n)
  (hk : n < k)
  (hlarge : n ! * 2 ^ (n - 1) < k) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_large_start hn hk hlarge


-- created on 2026-10-20
