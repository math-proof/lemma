/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean -/


import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry30Secondordereulerian.Part3
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 30 API checks

Local factors, coefficients at small arguments, and direct uses of the exported Euler product and
zeta identities.
-/


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry30Secondordereulerian

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry30Secondordereulerian

-- Local factors at exponents `0`, `1` and `5`.
example (a : ℕ → ℂ) (p : ℕ) : chapter5Entry30LocalCoeff a p 0 = 1 := by simp

example (a : ℕ → ℂ) (p : ℕ) : chapter5Entry30LocalCoeff a p 1 = a p := by simp

example (a : ℕ → ℂ) (p : ℕ) : chapter5Entry30LocalCoeff a p 5 = 0 :=
  chapter5Entry30LocalCoeff_of_two_le a p 5 (by norm_num)

-- Coefficients at `0`, `1`, a prime, a prime square and a product of two primes.
example (a : ℕ → ℂ) : chapter5Entry30Coeff a 0 = 0 := by simp

example (a : ℕ → ℂ) : chapter5Entry30Coeff a 1 = 1 := by simp

example (a : ℕ → ℂ) : chapter5Entry30Coeff a 3 = a 3 :=
  chapter5Entry30Coeff_prime a 3 Nat.prime_three

example (a : ℕ → ℂ) : chapter5Entry30Coeff a 9 = 0 := by
  simpa using chapter5Entry30Coeff_prime_pow_of_two_le a 3 2 Nat.prime_three le_rfl

example (a : ℕ → ℂ) : chapter5Entry30Coeff a 6 = a 2 * a 3 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, chapter5Entry30Coeff_mul_of_coprime a 2 3 (by norm_num),
    chapter5Entry30Coeff_prime a 2 Nat.prime_two, chapter5Entry30Coeff_prime a 3 Nat.prime_three]

-- The signed coefficient at the prime `2`.
example (s : ℂ) : chapter5Entry30SignedCoeff s 2 = -((2 : ℕ) : ℂ) ^ (-s) := by
  rw [chapter5Entry30SignedCoeff_of_ne_zero s 2 two_ne_zero]
  simp [Nat.prime_two.primeFactors, Nat.prime_two.prime.squarefree]

-- Terms of the three series at `n = 1` and `n = 2`.
example (s : ℂ) : chapter5Entry30SquarefreeTerm s 0 = 1 := by
  simp [chapter5Entry30SquarefreeTerm_def]

example (s : ℂ) : chapter5Entry30NonSquarefreeTerm s 0 = 0 := by
  simp [chapter5Entry30NonSquarefreeTerm_def]

example (s : ℂ) : chapter5Entry30OddTerm s 1 = ((2 : ℕ) : ℂ) ^ (-s) := by
  simp [chapter5Entry30OddTerm_def, Nat.prime_two.primeFactors, Nat.prime_two.prime.squarefree]

-- The Euler product as an unconditional product.
example (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    ∏' p : Nat.Primes, (1 + a p) = 1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2) :=
  (hasProd_one_add_chapter5Entry30Coeff a c hc ha).tprod_eq

-- The squarefree and non-squarefree series add up to `ζ(s)`.
example (s : ℂ) (hs : 1 < s.re) :
    ∑' j : ℕ, chapter5Entry30SquarefreeTerm s j +
      ∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j = riemannZeta s := by
  have h2re : 1 < (2 * s).re := by simp; linarith
  have hz2 := riemannZeta_ne_zero_of_one_lt_re h2re
  rw [tsum_chapter5Entry30SquarefreeTerm s hs, tsum_chapter5Entry30NonSquarefreeTerm s hs]
  field_simp
  ring

-- The odd squarefree series, cleared of denominators.
example (s : ℂ) (hs : 1 < s.re) :
    2 * riemannZeta s * riemannZeta (2 * s) * ∑' j : ℕ, chapter5Entry30OddTerm s j =
      riemannZeta s ^ 2 - riemannZeta (2 * s) := by
  have h2re : 1 < (2 * s).re := by simp; linarith
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 := riemannZeta_ne_zero_of_one_lt_re h2re
  rw [tsum_chapter5Entry30OddTerm s hs]
  field_simp

-- Summability of the three series.
example (s : ℂ) (hs : 1 < s.re) :
    Summable (chapter5Entry30SquarefreeTerm s) ∧ Summable (chapter5Entry30OddTerm s) ∧
      Summable (chapter5Entry30NonSquarefreeTerm s) :=
  ⟨summable_chapter5Entry30SquarefreeTerm s hs, summable_chapter5Entry30OddTerm s hs,
    summable_chapter5Entry30NonSquarefreeTerm s hs⟩

end MathlibExtTest.Analysis.Ramanujan.Part1Ch5Entry30Secondordereulerian
