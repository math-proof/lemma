import Mathlib.Probability.Independence.Integration
import sympy.stats.joint_rv
import sympy.stats.variance
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  {π : Measure Ω}
  {x : Ω → α}
  {f g : α → ℝ}
-- given
  [PSpace π x]
  (hf : Integrable f (π.map x))
  (hg : Integrable g (π.map x)) :
-- imply
  𝔼[x: π](f x) + 𝔼[x: π](g x) = 𝔼[x: π](f x + g x) := by
-- proof
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
  rw [integral_add hf hg]


-- created on 2023-04-12
