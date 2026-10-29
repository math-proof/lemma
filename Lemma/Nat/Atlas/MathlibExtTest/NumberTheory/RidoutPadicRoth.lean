import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.RidoutPadicRoth
open MathlibExtTest MathlibExtTest.NumberTheory MathlibExtTest.NumberTheory.RidoutPadicRoth


namespace MathlibExtTest.NumberTheory.RidoutPadicRoth

/--
[sqrt_two_isAlgebraic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RidoutPadicRoth.lean)
-/
@[path]
lemma sqrt_two_isAlgebraic :
-- imply
  IsAlgebraic ℚ (Real.sqrt 2) := by
-- proof
  apply IsIntegral.isAlgebraic
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 : ℚ),
    Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

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


-- created on 2026-10-23
-- updated on 2026-10-28
