import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.JordanTotient
open ArithmeticFunction


/--
[jordanTotient_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_zero_eq
  {k : ℕ} :
-- imply
  jordanTotient k 0 = 0 := by
-- proof
  apply ArithmeticFunction.jordanTotient_zero k

/--
[jordanTotient_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_apply_one_eq
  {k : ℕ} :
-- imply
  jordanTotient k 1 = 1 := by
-- proof
  apply ArithmeticFunction.jordanTotient_apply_one k

/--
[jordanTotient_eq_prod_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_eq_prod_factorization_eq
  {k n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  jordanTotient k n = ∏ p ∈ n.primeFactors,
    p ^ (k * (n.factorization p - 1)) * (p ^ k - 1) := by
-- proof
  apply ArithmeticFunction.jordanTotient_eq_prod_factorization hn

/--
[jordanTotient_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_prime_pow_eq
  {k p e : ℕ}
-- given
  (hp : p.Prime)
  (he : 0 < e) :
-- imply
  jordanTotient k (p ^ e) =
    p ^ (k * (e - 1)) * (p ^ k - 1) := by
-- proof
  apply ArithmeticFunction.jordanTotient_prime_pow hp he

/--
[jordanTotient_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_prime_eq
  {k p : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  jordanTotient k p = p ^ k - 1 := by
-- proof
  apply ArithmeticFunction.jordanTotient_prime hp

/--
[isMultiplicative_jordanTotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma isMultiplicative_jordanTotient_eq
  {k : ℕ} :
-- imply
  IsMultiplicative (jordanTotient k) := by
-- proof
  apply ArithmeticFunction.isMultiplicative_jordanTotient k

/--
[jordanTotient_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_one_apply_eq
  {n : ℕ} :
-- imply
  jordanTotient 1 n = n.totient := by
-- proof
  apply ArithmeticFunction.jordanTotient_one_apply n

/--
[jordanTotient_eq_sum_moebius](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_eq_sum_moebius_eq
  {k n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  ((jordanTotient k n : ℕ) : ℤ) =
    ∑ d ∈ n.divisors, moebius (n / d) * (d : ℤ) ^ k := by
-- proof
  apply ArithmeticFunction.jordanTotient_eq_sum_moebius hn

/--
[jordanTotient_mul_prod_primeFactors_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_mul_prod_primeFactors_pow_eq
  {k n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  jordanTotient k n * ∏ p ∈ n.primeFactors, p ^ k =
    n ^ k * ∏ p ∈ n.primeFactors, (p ^ k - 1) := by
-- proof
  apply ArithmeticFunction.jordanTotient_mul_prod_primeFactors_pow hn

/--
[jordanTotient_eq_rational_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/JordanTotient.lean)
-/
@[path]
private lemma jordanTotient_eq_rational_prod_eq
  {k n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  ((jordanTotient k n : ℕ) : ℚ) =
    (n : ℚ) ^ k *
    ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℚ) ^ k) := by
-- proof
  apply ArithmeticFunction.jordanTotient_eq_rational_prod hn


-- created on 2026-10-20
