/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ArithmeticFunction/DedekindPsi.lean -/


import Def.NumberTheory.ArithmeticFunction.DedekindPsi
import Lemma.Nat.ArithmeticFunction.DedekindPsi
open ArithmeticFunction


example : dedekindPsi 0 = 0 := by simp

example : dedekindPsi 1 = 1 := by simp

example : dedekindPsi 2 = 3 :=
  dedekindPsi_prime (by decide)

example : dedekindPsi (2 ^ 2) = 6 := by
  simpa using dedekindPsi_prime_pow (p := 2) (k := 2) (by decide) (by decide)

example : dedekindPsi 6 = 12 := by
  have h : dedekindPsi (2 * 3) = dedekindPsi 2 * dedekindPsi 3 :=
    isMultiplicative_dedekindPsi.map_mul_of_coprime (by decide)
  simpa [dedekindPsi_prime (by decide : Nat.Prime 2),
    dedekindPsi_prime (by decide : Nat.Prime 3)] using h

example : dedekindPsi 12 = 24 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by decide]
  rw [isMultiplicative_dedekindPsi.map_mul_of_coprime (by decide)]
  rw [dedekindPsi_prime_pow (by decide) (by decide), dedekindPsi_prime (by decide)]
  rfl

example : dedekindPsi 12 * ∏ p ∈ (12 : ℕ).primeFactors, p =
    (12 : ℕ) * ∏ p ∈ (12 : ℕ).primeFactors, (p + 1) :=
  dedekindPsi_mul_prod_primeFactors (by decide)

example : (dedekindPsi 12 : ℚ) =
    (12 : ℚ) * ∏ p ∈ (12 : ℕ).primeFactors, (1 + (p : ℚ)⁻¹) :=
  dedekindPsi_eq_rational_prod (by decide)

