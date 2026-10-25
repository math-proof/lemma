/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RidoutPadicRoth.lean -/


import Def.NumberTheory.RidoutPadicRoth
import Lemma.Nat.RidoutPadicRoth
import Mathlib.RingTheory.Algebraic.Integral


namespace MathlibExtTest.NumberTheory.RidoutPadicRoth

-- Ridout's theorem applies to `√2`, exponent `5/2`, and the prime `2`.
example : Set.Finite {r : ℚ |
    ((∏ l ∈ ({⟨2, Nat.prime_two⟩} : Finset Nat.Primes),
      padicNorm l.1 (r.num : ℚ) * padicNorm l.1 (r.den : ℚ) : ℚ) : ℝ) *
        |Real.sqrt 2 - (r : ℝ)| <
      (((max r.num.natAbs r.den : ℕ) : ℝ) ^ (2 + (1 / 2 : ℝ)))⁻¹} := by
  apply MetaMathlibExt.ridout_padic_roth (Real.sqrt 2)
  · exact sqrt_two_isAlgebraic
  · exact irrational_sqrt_two
  · norm_num

end MathlibExtTest.NumberTheory.RidoutPadicRoth
