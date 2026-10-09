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
  {f : α → ℝ}
-- given
  [PSpace π x]
  (hb : BddBelow (Set.range f))
  (hf : Integrable f (π.map x)) :
-- imply
  ⨅ a, f a ≤ 𝔼[x: π](f x) := by
-- proof
  have : IsProbabilityMeasure (π.map x) := inferInstance
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
  calc _ = ∫ _, (⨅ a, f a) ∂(π.map x) := by simp
    _ ≤ ∫ a, f a ∂(π.map x) := integral_mono (integrable_const _) hf (fun a => ciInf_le hb a)


-- created on 2023-04-04
