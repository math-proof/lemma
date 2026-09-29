import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
  {c : ℝ}
-- given
  [PSpace π x]
  [PSpace π (fun ω => c * x ω)] :
-- imply
  Variance π (fun ω => c * x ω) = c ^ 2 * Variance π x := by
-- proof
  have e : ∀ ω, (c * x ω - c * ∫ ω', x ω' ∂π) ^ 2 = c ^ 2 * (x ω - ∫ ω', x ω' ∂π) ^ 2 := fun ω => by ring
  simp only [Variance.eq_integral, integral_const_mul, e]


-- created on 2026-09-27
