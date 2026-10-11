import Mathlib
import sympy.Basic
import sympy.functions.special.CatalanConstant


/--
[CatalanConstant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CatalanConstant.lean)
-/
@[path]
private lemma summable_catalan_constant_terms_is :
-- imply
  Summable (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) := by
-- proof
  apply Real.summable_catalanConstant_terms

/--
[CatalanConstant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CatalanConstant.lean)
-/
@[path]
private lemma catalan_constant_eq_tsum_eq :
-- imply
  Real.catalanConstant = ∑' n : ℕ, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
-- proof
  apply Real.catalanConstant_eq_tsum

/--
[CatalanConstant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CatalanConstant.lean)
-/
@[path]
private lemma has_sum_catalan_constant_is :
-- imply
  HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2) Real.catalanConstant := by
-- proof
  apply Real.hasSum_catalanConstant


-- created on 2026-10-11
