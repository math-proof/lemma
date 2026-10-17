import Mathlib.Probability.Distributions.Gaussian.Real
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
The Gaussian probability of an interval is the integral of its density, i.e. the distribution
function whose derivative is `gaussianPDFReal`.
-/
@[path]
private lemma main
  {μ : ℝ}
  {v : NNReal}
  (s : Set ℝ)
-- given
  (h₀ : v ≠ 0) :
-- imply
  gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v x) :=
-- proof
  gaussianReal_apply_eq_integral μ h₀ s


-- created on 2026-10-11
-- updated on 2026-10-17
