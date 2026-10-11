import Mathlib
import sympy.Basic
import sympy.functions.special.gamma.Digamma


/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma summable_one_div_add_nat_succ_sq_is :
-- imply
  Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
-- proof
  apply Real.summable_one_div_add_nat_succ_sq

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma has_sum_digamma_series_is
-- given
  (x : ℝ)
  (hx : 0 < x) :
-- imply
  HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1))
    (deriv (fun t => Real.log (Real.Gamma t)) (x + 1)
      + Real.eulerMascheroniConstant) := by
-- proof
  apply Real.hasSum_digamma_series x hx

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma has_deriv_at_tsum_digamma_series_is
-- given
  (y : ℝ)
  (hy : 0 < y) :
-- imply
  HasDerivAt (fun z => ∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / (z + (j : ℝ) + 1)))
    (∑' j : ℕ, 1 / (y + (j : ℝ) + 1) ^ 2) y := by
-- proof
  apply Real.hasDerivAt_tsum_digamma_series y hy

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma deriv_deriv_log_gamma_add_one_eq
-- given
  (y : ℝ)
  (hy : 0 < y) :
-- imply
  deriv (deriv (fun t => Real.log (Real.Gamma t))) (y + 1)
    = ∑' j : ℕ, 1 / (y + (j : ℝ) + 1) ^ 2 := by
-- proof
  apply Real.deriv_deriv_log_Gamma_add_one y hy

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma deriv_log_gamma_eq
-- given
  (u : ℝ)
  (hu : 0 < u) :
-- imply
  deriv (fun t => Real.log (Real.Gamma t)) u
    = deriv Real.Gamma u / Real.Gamma u := by
-- proof
  apply Real.deriv_log_Gamma u hu


-- created on 2026-10-11
