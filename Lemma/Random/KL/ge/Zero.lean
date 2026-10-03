import Mathlib.InformationTheory.KullbackLeibler.Basic
import sympy.Basic
open MeasureTheory InformationTheory


/--
Gibbs' inequality: the Kullback-Leibler divergence `KL(Pr[θ](x) ‖ Pr[θ'](x))` between the laws
of a random variable `x` under two probability measures is nonnegative.

Python: Random.KL.ge.Zero (the py proof expands `KL` as `∑ₓ p(x) * log (p(x) / q(x))`, bounds
`log t ≥ 1 - 1 / t` and sums; here the general measure-theoretic form, with `KL` written as the
integral of the log-likelihood ratio `llr` against the law of `x`).
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α]
  {π π' : Measure Ω}
  {x : Ω → α}
  [IsProbabilityMeasure π]
  [IsProbabilityMeasure π']
-- given
  (hx : Measurable x)
  (h_ac : π.map x ≪ π'.map x)
  (h_int : Integrable (llr (π.map x) (π'.map x)) (π.map x)) :
-- imply
  ∫ a, llr (π.map x) (π'.map x) a ∂(π.map x) ≥ 0 := by
-- proof
  have : IsProbabilityMeasure (π.map x) := Measure.isProbabilityMeasure_map hx.aemeasurable
  have : IsProbabilityMeasure (π'.map x) := Measure.isProbabilityMeasure_map hx.aemeasurable
  have h := integral_llr_add_sub_measure_univ_nonneg h_ac h_int
  simpa [Measure.real] using h


-- created on 2021-07-20