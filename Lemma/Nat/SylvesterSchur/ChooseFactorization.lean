import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur.ChooseFactorization
open scoped BigOperators
open Finset Nat
open Nat.SylvesterSchur


/--
[choose_eq_prod_small_prime_powers_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_eq_prod_small_prime_powers_of_no_large_eq
  {N r : ℕ}
-- given
  (hrN : r ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  (∏ p ∈ Finset.range (r + 1), p ^ (Nat.choose N r).factorization p) =
    Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.choose_eq_prod_small_prime_powers_of_no_large hrN hsmall

/--
[choose_le_top_pow_primeCounting_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_le_top_pow_primeCounting_of_no_large_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  Nat.choose N r ≤ N ^ Nat.primeCounting r := by
-- proof
  apply Nat.SylvesterSchur.choose_le_top_pow_primeCounting_of_no_large hN hrN hsmall

/--
[choose_le_top_pow_sub_one_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_le_top_pow_sub_one_of_no_large_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hr : 2 ≤ r)
  (hrN : r ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  Nat.choose N r ≤ N ^ (r - 1) := by
-- proof
  apply Nat.SylvesterSchur.choose_le_top_pow_sub_one_of_no_large hN hr hrN hsmall

/--
[choose_le_top_pow_half_add_one_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_le_top_pow_half_add_one_of_no_large_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  Nat.choose N r ≤ N ^ (r / 2 + 1) := by
-- proof
  apply Nat.SylvesterSchur.choose_le_top_pow_half_add_one_of_no_large hN hrN hsmall

/--
[choose_le_top_pow_three_mul_div_eight_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_le_top_pow_three_mul_div_eight_of_no_large_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hr : 38 ≤ r)
  (hrN : r ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  Nat.choose N r ≤ N ^ (3 * r / 8) := by
-- proof
  apply Nat.SylvesterSchur.choose_le_top_pow_three_mul_div_eight_of_no_large hN hr hrN hsmall

/--
[choose_le_prod_primorial_nthRoot_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_le_prod_primorial_nthRoot_of_no_large_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  Nat.choose N r ≤
    ∏ j ∈ Finset.range (Nat.log 2 N), primorial (Nat.nthRoot (j + 1) N) := by
-- proof
  apply Nat.SylvesterSchur.choose_le_prod_primorial_nthRoot_of_no_large hN hrN hsmall

/--
[choose_le_prod_erdos_layers_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_le_prod_erdos_layers_of_no_large_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  Nat.choose N r ≤
    ∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N) := by
-- proof
  apply Nat.SylvesterSchur.choose_le_prod_erdos_layers_of_no_large hN hrN hsmall

/--
[choose_le_prod_erdos_div_three_layers_of_no_large](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ChooseFactorization.lean)
-/
@[path]
private lemma choose_le_prod_erdos_div_three_layers_of_no_large_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (h2rN : 2 * r ≤ N)
  (hN6 : 6 ≤ N)
  (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  Nat.choose N r ≤
    ∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N) := by
-- proof
  apply Nat.SylvesterSchur.choose_le_prod_erdos_div_three_layers_of_no_large hN hrN h2rN hN6 hsmall


-- created on 2026-10-20
