/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/


import Def.NumberTheory.PrimeCounting.ArithmeticLargeSieve.Part3
import Lemma.Nat.PrimeCounting.ArithmeticLargeSieve
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.NumberTheory.PrimeCounting.ArithmeticLargeSieve

open scoped BigOperators

open MathlibExt.NumberTheory.PrimeCounting

-- Apply the progression large sieve to the singleton producing the prime two.
example :
    (∑ r ∈ Finset.Icc 1 (1 : ℕ),
        ((1 : ℝ) + 3 * (r : ℝ) / 2)⁻¹ *
          (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) *
        ({0} : Finset ℕ).card ^ 2 ≤
      ((1 : ℝ) / Nat.totient 1) * ({0} : Finset ℕ).card := by
  have hS : ({0} : Finset ℕ) ⊆ Finset.range 1 := by simp
  have hprime : ∀ n ∈ ({0} : Finset ℕ), (1 * n + 2).Prime := by
    intro n hn
    simp only [Finset.mem_singleton] at hn
    subst n
    exact Nat.prime_two
  have hlarge : ∀ n ∈ ({0} : Finset ℕ), 1 < 1 * n + 2 := by
    intro n hn
    simp only [Finset.mem_singleton] at hn
    subst n
    norm_num
  simpa only [Nat.cast_one, one_mul, mul_one] using
    arithmeticLargeSieve_progression 1 1 1 2 (by norm_num) (by norm_num)
      ({0} : Finset ℕ) hS hprime hlarge

end MathlibExtTest.NumberTheory.PrimeCounting.ArithmeticLargeSieve
