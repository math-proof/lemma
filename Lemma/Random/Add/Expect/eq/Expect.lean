import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  {π : Measure Ω}
  {x : Ω → α}
  {f g : α → ℝ}
-- given
  [PSpace π x]
  (hf : Integrable f (π.map x))
  (hg : Integrable g (π.map x))
  (c d : ℝ) :
-- imply
  c * 𝔼[x: π](f x) + d * 𝔼[x: π](g x) = 𝔼[x: π](c * f x + d * g x) := by
-- proof
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
  rw [integral_add (hf.const_mul c) (hg.const_mul d), integral_const_mul, integral_const_mul]


-- created on 2023-04-13
