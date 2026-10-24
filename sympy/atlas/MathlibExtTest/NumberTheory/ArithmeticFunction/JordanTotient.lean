/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ArithmeticFunction/JordanTotient.lean -/

import sympy.atlas.NumberTheory.ArithmeticFunction.JordanTotient
import Lemma.Nat.ArithmeticFunction.JordanTotient
/-!
# Examples for Jordan totient
Boundary values, totient specialization, and source orientation.
-/
namespace JordanTotientTest
open ArithmeticFunction
example (k : ℕ) : jordanTotient k 0 = 0 :=
  ArithmeticFunction.jordanTotient_zero k
example (k : ℕ) : jordanTotient k 1 = 1 :=
  ArithmeticFunction.jordanTotient_apply_one k
example : jordanTotient 1 12 = 4 := by
  have h := ArithmeticFunction.jordanTotient_one_apply 12
  have ht : Nat.totient 12 = 4 := by decide
  rw [h]
  exact ht
example : Nat.totient 12 = 4 := by decide
example : jordanTotient 1 12 = Nat.totient 12 :=
  ArithmeticFunction.jordanTotient_one_apply 12
example : jordanTotient 2 2 = 3 := by
  have h := ArithmeticFunction.jordanTotient_prime (k := 2) (p := 2)
    (by decide : Nat.Prime 2)
  have h3 : (2 : ℕ) ^ 2 - 1 = 3 := by decide
  rwa [h3] at h
example : jordanTotient 2 3 = 8 := by
  have h := ArithmeticFunction.jordanTotient_prime (k := 2) (p := 3)
    (by decide : Nat.Prime 3)
  have h8 : (3 : ℕ) ^ 2 - 1 = 8 := by decide
  rwa [h8] at h
example : jordanTotient 1 5 = 4 := by
  have h := ArithmeticFunction.jordanTotient_prime (k := 1) (p := 5)
    (by decide : Nat.Prime 5)
  have h4 : (5 : ℕ) ^ 1 - 1 = 4 := by decide
  rwa [h4] at h
example : jordanTotient 2 4 = 12 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by decide
  have h := ArithmeticFunction.jordanTotient_prime_pow (k := 2)
    (p := 2) (e := 2) (by decide : Nat.Prime 2) (by decide : 0 < 2)
  have hval : (2 : ℕ) ^ (2 * (2 - 1)) * (2 ^ 2 - 1) = 12 := by decide
  rw [h4, h]
  exact hval
example : jordanTotient 2 8 = 48 := by
  have h8 : (8 : ℕ) = 2 ^ 3 := by decide
  have h := ArithmeticFunction.jordanTotient_prime_pow (k := 2)
    (p := 2) (e := 3) (by decide : Nat.Prime 2) (by decide : 0 < 3)
  have hval : (2 : ℕ) ^ (2 * (3 - 1)) * (2 ^ 2 - 1) = 48 := by decide
  rw [h8, h]
  exact hval
example : jordanTotient 1 8 = 4 := by
  have h8 : (8 : ℕ) = 2 ^ 3 := by decide
  have h := ArithmeticFunction.jordanTotient_prime_pow (k := 1)
    (p := 2) (e := 3) (by decide : Nat.Prime 2) (by decide : 0 < 3)
  have hval : (2 : ℕ) ^ (1 * (3 - 1)) * (2 ^ 1 - 1) = 4 := by decide
  rw [h8, h]
  exact hval
example : jordanTotient 2 6 = 24 := by
  have h6 : (6 : ℕ) = 2 * 3 := by decide
  have hcop : Nat.Coprime 2 3 := by decide
  have hmul := ArithmeticFunction.isMultiplicative_jordanTotient 2
  have h2 := ArithmeticFunction.jordanTotient_prime (k := 2) (p := 2)
    (by decide : Nat.Prime 2)
  have h3 := ArithmeticFunction.jordanTotient_prime (k := 2) (p := 3)
    (by decide : Nat.Prime 3)
  have v2 : (2 : ℕ) ^ 2 - 1 = 3 := by decide
  have v3 : (3 : ℕ) ^ 2 - 1 = 8 := by decide
  have v6 : (3 : ℕ) * 8 = 24 := by decide
  rw [h6, hmul.map_mul_of_coprime hcop, h2, h3, v2, v3]
  exact v6
example : jordanTotient 2 12 = 96 := by
  have h12 : (12 : ℕ) = 4 * 3 := by decide
  have hcop : Nat.Coprime 4 3 := by decide
  have hmul := ArithmeticFunction.isMultiplicative_jordanTotient 2
  have h4 : (4 : ℕ) = 2 ^ 2 := by decide
  have hp4 := ArithmeticFunction.jordanTotient_prime_pow (k := 2)
    (p := 2) (e := 2) (by decide : Nat.Prime 2) (by decide : 0 < 2)
  have h3 := ArithmeticFunction.jordanTotient_prime (k := 2) (p := 3)
    (by decide : Nat.Prime 3)
  have v4 : (2 : ℕ) ^ (2 * (2 - 1)) * (2 ^ 2 - 1) = 12 := by decide
  have v3 : (3 : ℕ) ^ 2 - 1 = 8 := by decide
  have v12 : (12 : ℕ) * 8 = 96 := by decide
  have hJ4 : jordanTotient 2 4 = 12 := by
    rw [h4, hp4]
    exact v4
  rw [h12, hmul.map_mul_of_coprime hcop, hJ4, h3, v3]
  exact v12
example : ((jordanTotient 2 1 : ℕ) : ℚ) =
      (1 : ℚ) ^ 2 *
        ∏ p ∈ (1 : ℕ).primeFactors, (1 - 1 / (p : ℚ) ^ 2) :=
  ArithmeticFunction.jordanTotient_eq_rational_prod (by decide)
example : ((jordanTotient 2 6 : ℕ) : ℤ) =
      ∑ d ∈ (6 : ℕ).divisors,
        ArithmeticFunction.moebius (6 / d) * (d : ℤ) ^ 2 :=
  ArithmeticFunction.jordanTotient_eq_sum_moebius (by decide)
example : ((jordanTotient 2 12 : ℕ) : ℤ) =
      ∑ d ∈ (12 : ℕ).divisors,
        ArithmeticFunction.moebius (12 / d) * (d : ℤ) ^ 2 :=
  ArithmeticFunction.jordanTotient_eq_sum_moebius (by decide)
example : jordanTotient 1 12 = Nat.totient 12 :=
  ArithmeticFunction.jordanTotient_one_apply 12
end JordanTotientTest
