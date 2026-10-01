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
  (hb : BddAbove (Set.range f))
  (hf : Integrable f (π.map x)) :
-- imply
  𝔼[x: π](f x) ≤ ⨆ a, f a := by
-- proof
  have := Measure.isProbabilityMeasure_map (PSpace.aemeasurable (π := π) (x := x))
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
  calc ∫ a, f a ∂(π.map x) ≤ ∫ _a, (⨆ a, f a) ∂(π.map x) := integral_mono hf (integrable_const _) (fun a => le_ciSup hb a)
    _ = ⨆ a, f a := by simp


-- created on 2023-04-04
