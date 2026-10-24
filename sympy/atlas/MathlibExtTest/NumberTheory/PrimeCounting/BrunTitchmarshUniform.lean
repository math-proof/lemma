/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/BrunTitchmarshUniform.lean -/


import sympy.atlas.NumberTheory.PrimeCounting.BrunTitchmarshUniform
import Lemma.Nat.PrimeCounting.BrunTitchmarshUniform
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega


namespace MathlibExtTest.NumberTheory.PrimeCounting.BrunTitchmarshUniform

open MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted

-- At exponent `1/2`, the theorem bounds primes congruent to `1` modulo `4` for `X ≥ 16`.
example : ∃ ξ₁ : ℝ, 0 < ξ₁ ∧ ∀ X : ℕ, 16 ≤ X →
    (Nat.primeCountingMod X 4 1 : ℝ) <
      ξ₁ * (X : ℝ) /
        ((Nat.totient 4 : ℝ) * Real.log ((X : ℝ) / 4)) := by
  obtain ⟨ξ₁, hξ₁, hbound⟩ :=
    brun_titchmarsh_uniform (1 / 2 : ℝ) (by norm_num) (by norm_num)
  refine ⟨ξ₁, hξ₁, ?_⟩
  intro X hX
  apply hbound X 4 1 (by omega) (by norm_num)
  have hpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ 16 by norm_num)
    (show (16 : ℝ) ≤ X by exact_mod_cast hX) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  norm_num at hpow
  exact hpow

end MathlibExtTest.NumberTheory.PrimeCounting.BrunTitchmarshUniform
