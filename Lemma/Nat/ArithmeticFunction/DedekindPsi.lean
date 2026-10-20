import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.DedekindPsi
open Nat Finset
open ArithmeticFunction


/--
[dedekindPsi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma dedekindPsi_zero_eq
  :
-- imply
  dedekindPsi (0 : ℕ) = 0 := by
-- proof
  apply ArithmeticFunction.dedekindPsi_zero

/--
[dedekindPsi_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma dedekindPsi_one_eq
  :
-- imply
  dedekindPsi (1 : ℕ) = 1 := by
-- proof
  apply ArithmeticFunction.dedekindPsi_one

/--
[dedekindPsi_eq_prod_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma dedekindPsi_eq_prod_factorization_eq
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  dedekindPsi n = n.factorization.prod fun p k => p ^ (k - 1) * (p + 1) := by
-- proof
  apply ArithmeticFunction.dedekindPsi_eq_prod_factorization hn

/--
[dedekindPsi_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma dedekindPsi_prime_pow_eq
  {p k : ℕ}
-- given
  (hp : Nat.Prime p)
  (hk : 0 < k) :
-- imply
  dedekindPsi (p ^ k) = p ^ (k - 1) * (p + 1) := by
-- proof
  apply ArithmeticFunction.dedekindPsi_prime_pow hp hk

/--
[dedekindPsi_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma dedekindPsi_prime_eq
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  dedekindPsi p = p + 1 := by
-- proof
  apply ArithmeticFunction.dedekindPsi_prime hp

/--
[isMultiplicative_dedekindPsi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma isMultiplicative_dedekindPsi_eq
  :
-- imply
  IsMultiplicative dedekindPsi := by
-- proof
  apply ArithmeticFunction.isMultiplicative_dedekindPsi

/--
[dedekindPsi_mul_prod_primeFactors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma dedekindPsi_mul_prod_primeFactors_eq
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  dedekindPsi n * ∏ p ∈ n.primeFactors, p = n * ∏ p ∈ n.primeFactors, (p + 1) := by
-- proof
  apply ArithmeticFunction.dedekindPsi_mul_prod_primeFactors hn

/--
[dedekindPsi_eq_rational_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/DedekindPsi.lean)
-/
@[path]
private lemma dedekindPsi_eq_rational_prod_eq
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  (dedekindPsi n : ℚ) = (n : ℚ) * ∏ p ∈ n.primeFactors, (1 + (p : ℚ)⁻¹) := by
-- proof
  apply ArithmeticFunction.dedekindPsi_eq_rational_prod hn


-- created on 2026-10-20
