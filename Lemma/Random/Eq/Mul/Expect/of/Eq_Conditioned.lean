import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
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
    Expectation.ofRV_eq_integral (f := fun p : ℝ × ℝ => p.1 * p.2) (Continuous.aestronglyMeasurable (by fun_prop))
  have h2 : 𝔼[x: π](x) = ∫ ω, x ω ∂π := Expectation.ofRV_self π x
  have h3 : 𝔼[y: π](y) = ∫ ω, y ω ∂π := Expectation.ofRV_self π y
  rw [h1, h2, h3]
  exact h.integral_mul_eq_mul_integral (PSpace.aemeasurable (π := π) (x := x)).aestronglyMeasurable (PSpace.aemeasurable (π := π) (x := y)).aestronglyMeasurable


-- created on 2026-09-27
