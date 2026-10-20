import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.LaplaceTheta
open MeasureTheory Finset
open Chebyshev


/--
[laplace_theta_exp_eq_primeLogSeries_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/LaplaceTheta.lean)
-/
@[path]
private lemma laplace_theta_exp_eq_primeLogSeries_div_eq
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  laplace (fun t : ℝ => (theta (Real.exp t) : ℂ)) s =
    primeLogSeries s / s := by
-- proof
  apply Chebyshev.laplace_theta_exp_eq_primeLogSeries_div s hs

/--
[hasLaplace_theta_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/LaplaceTheta.lean)
-/
@[path]
private lemma hasLaplace_theta_exp_eq
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  HasLaplace (fun t : ℝ => (theta (Real.exp t) : ℂ)) s
    (primeLogSeries s / s) := by
-- proof
  apply Chebyshev.hasLaplace_theta_exp s hs

/--
[differentiableOn_laplace_theta_exp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/LaplaceTheta.lean)
-/
@[path]
private lemma differentiableOn_laplace_theta_exp_eq
  :
-- imply
  DifferentiableOn ℂ (laplace (fun t : ℝ => (theta (Real.exp t) : ℂ)))
    {s | 1 < s.re} := by
-- proof
  apply Chebyshev.differentiableOn_laplace_theta_exp


-- created on 2026-10-20
