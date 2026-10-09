import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.Wirtinger

open Real.Calculus.Wirtinger

/--
[wirtinger_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Wirtinger.lean)
-/
@[path]
private lemma wirtinger_inequality_eq
-- given
  (f f' : ℝ → ℝ)
  (hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi,
    HasDerivWithinAt f (f' x) (Set.Icc 0 Real.pi) x)
  (hf_deriv_cont : ContinuousOn f' (Set.Icc 0 Real.pi))
  (h0 : f 0 = 0) (hpi : f Real.pi = 0) :
-- imply
  intervalIntegral (fun x => (f x) ^ 2) 0 Real.pi MeasureTheory.volume ≤
    intervalIntegral (fun x => (f' x) ^ 2) 0 Real.pi MeasureTheory.volume := by
-- proof
  apply wirtinger_inequality f f' hf_deriv hf_deriv_cont h0 hpi


-- created on 2026-10-09
