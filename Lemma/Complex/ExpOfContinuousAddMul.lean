import Mathlib
import sympy.Basic
import sympy.functions.special.ExpOfContinuousAddMul


/--
[ExpOfContinuousAddMul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpOfContinuousAddMul.lean)
-/
@[path]
private lemma exists_eq_exp_mul_of_continuous_add_mul_is
-- given
  (f : ℝ → ℂ)
  (hf : Continuous f)
  (hzero : f 0 = 1)
  (hadd : ∀ r : ℝ, ∀ s : ℝ, f (r + s) = f r * f s) :
-- imply
  ∃ L : ℂ, ∀ r : ℝ, f r = Complex.exp ((r : ℂ) * L) := by
-- proof
  apply MetaMathlibExt.exists_eq_exp_mul_of_continuous_add_mul f hf hzero hadd


-- created on 2026-10-11
