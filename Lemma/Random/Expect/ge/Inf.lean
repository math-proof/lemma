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
  {f : α → ℝ}
-- given
  [PSpace π x]
  (hb : BddBelow (Set.range f))
  (hf : Integrable f (π.map x)) :
-- imply
  𝔼[x: π](f x) ≥ ⨅ a, f a := by
-- proof
  have := Measure.isProbabilityMeasure_map (PSpace.aemeasurable (π := π) (x := x))
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real, ge_iff_le]
  calc ⨅ a, f a = ∫ _a, (⨅ a, f a) ∂(π.map x) := by simp
    _ ≤ ∫ a, f a ∂(π.map x) := integral_mono (integrable_const _) hf (fun a => ciInf_le hb a)


-- created on 2026-09-27
