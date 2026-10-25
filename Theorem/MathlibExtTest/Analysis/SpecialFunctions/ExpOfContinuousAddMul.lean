/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ExpOfContinuousAddMul.lean -/


import Lemma.Complex.ExpOfContinuousAddMul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


namespace MathlibExtTest.Analysis.SpecialFunctions.ExpOfContinuousAddMul

open MetaMathlibExt

-- Checks that the exponential classification forces differentiability.
example (f : ℝ → ℂ) (hf : Continuous f) (hzero : f 0 = 1)
    (hadd : ∀ r s : ℝ, f (r + s) = f r * f s) : Differentiable ℝ f := by
  obtain ⟨L, hL⟩ := exists_eq_exp_mul_of_continuous_add_mul f hf hzero hadd
  rw [show f = fun r : ℝ => Complex.exp ((r : ℂ) * L) from funext hL]
  intro r
  exact (((hasDerivAt_mul_const L).comp_ofReal).cexp).differentiableAt

-- Checks that the exponential classification rules out zeros.
example (f : ℝ → ℂ) (hf : Continuous f) (hzero : f 0 = 1)
    (hadd : ∀ r s : ℝ, f (r + s) = f r * f s) : ∀ r : ℝ, f r ≠ 0 := by
  obtain ⟨L, hL⟩ := exists_eq_exp_mul_of_continuous_add_mul f hf hzero hadd
  intro r
  rw [hL r]
  exact Complex.exp_ne_zero _

end MathlibExtTest.Analysis.SpecialFunctions.ExpOfContinuousAddMul
