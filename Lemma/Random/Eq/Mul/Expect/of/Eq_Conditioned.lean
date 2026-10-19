import Mathlib.Probability.Independence.Integration
import sympy.stats.variance
import Lemma.Random.Expect.eq.Integral.Id
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y : Ω → ℝ}
-- given
  [PSpace π x]
  [PSpace π y]
  (h : ProbabilityTheory.IndepFun x y π) :
-- imply
  𝔼[x, y: π](x * y) = 𝔼[x: π](x) * 𝔼[y: π](y) := by
-- proof
  have h1 : 𝔼[x, y: π](x * y) = ∫ ω, x ω * y ω ∂π :=
    Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map (f := fun p : ℝ × ℝ => p.1 * p.2) (Continuous.aestronglyMeasurable (by fun_prop))
  have h2 : 𝔼[x: π](x) = ∫ ω, x ω ∂π := Random.Expect.eq.Integral.Id
  have h3 : 𝔼[y: π](y) = ∫ ω, y ω ∂π := Random.Expect.eq.Integral.Id
  rw [h1, h2, h3]
  exact h.integral_mul_eq_mul_integral (PSpace.aemeasurable (π := π) (x := x)).aestronglyMeasurable (PSpace.aemeasurable (π := π) (x := y)).aestronglyMeasurable


-- created on 2023-04-09
