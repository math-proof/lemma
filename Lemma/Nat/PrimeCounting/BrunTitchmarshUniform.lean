import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.BrunTitchmarshUniform
open MathlibExt.SelbergSieve
open MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted


/--
[brun_titchmarsh_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTitchmarshUniform.lean)
-/
@[path]
private lemma brun_titchmarsh_uniform_eq
  {β : ℝ}
-- given
  (hβ0 : 0 < β)
  (hβ1 : β < 1) :
-- imply
  ∃ ξ₁ : ℝ, 0 < ξ₁ ∧ ∀ X k ell : ℕ, 2 ≤ X → 1 ≤ k →
    (k : ℝ) ≤ Real.rpow (X : ℝ) β →
    (Nat.primeCountingMod X k ell : ℝ) <
    ξ₁ * (X : ℝ) / ((Nat.totient k : ℝ) * Real.log ((X : ℝ) / (k : ℝ))) := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted.brun_titchmarsh_uniform β hβ0 hβ1


-- created on 2026-10-20
