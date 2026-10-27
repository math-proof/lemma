import Mathlib.Probability.Independence.Integration
import Syntax.Probability.JointRv.Part6
import Theorem.Function
open MeasureTheory


/-!
[sympy.Variance / sympy.Covariance](https://github.com/sympy/sympy/blob/master/sympy/stats/symbolic_probability.py)
for real random variables, built on `Expectation.ofRV` (the `𝔼[x: π](…)` of `Syntax.Probability.JointRv.Part6`)
with the `Expectation ℝ` (Bochner) instance. Only the weak `PSpace` is needed.
-/

/-- Two random variables with probability spaces span one jointly: the pair is a.e. measurable. -/
instance PSpace.joint
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {π : Measure Ω} {x : Ω → α} {y : Ω → β} [hx : PSpace π x] [hy : PSpace π y] :
    PSpace π (x, y) where
  toIsProbabilityMeasure := hx.toIsProbabilityMeasure
  aemeasurable := hx.aemeasurable.prodMk hy.aemeasurable

