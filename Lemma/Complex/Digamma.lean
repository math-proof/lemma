import Mathlib
import sympy.Basic
import sympy.functions.special.gamma.Digamma


/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma analytic_at_gamma_is
-- given
  (w : ℂ)
  (hw : ∀ m : ℕ, w ≠ -((m : ℕ) : ℂ)) :
-- imply
  AnalyticAt ℂ Complex.Gamma w := by
-- proof
  apply Complex.analyticAt_Gamma w hw

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma analytic_at_digamma_is
-- given
  (w : ℂ)
  (hw : ∀ m : ℕ, w ≠ -((m : ℕ) : ℂ)) :
-- imply
  AnalyticAt ℂ Complex.digamma w := by
-- proof
  apply Complex.analyticAt_digamma w hw

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma deriv_gamma_of_real_eq
-- given
  (t : ℝ)
  (ht : 0 < t) :
-- imply
  deriv Complex.Gamma (↑t) = ↑(deriv Real.Gamma t) := by
-- proof
  apply Complex.deriv_Gamma_ofReal t ht

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma summable_norm_one_div_add_nat_succ_sq_is
-- given
  (z : ℂ) :
-- imply
  Summable (fun k : ℕ => ‖(1 / (z + (k + 1 : ℕ)) ^ 2 : ℂ)‖) := by
-- proof
  apply Complex.summable_norm_one_div_add_nat_succ_sq z

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma summable_digamma_series_term_is
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  Summable (fun j : ℕ => Complex.digammaSeriesTerm j s) := by
-- proof
  apply Complex.summable_digammaSeriesTerm s hs

/--
[Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/Digamma.lean)
-/
@[path]
private lemma has_sum_digamma_series_is
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  HasSum (fun j : ℕ => Complex.digammaSeriesTerm j s)
    (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) := by
-- proof
  apply Complex.hasSum_digamma_series s hs


-- created on 2026-10-11
