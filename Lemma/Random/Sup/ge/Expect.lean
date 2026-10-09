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
  (hb : BddAbove (Set.range f))
  (hf : Integrable f (π.map x)) :
-- imply
  ⨆ a, f a ≥ 𝔼[x: π](f x) := by
-- proof
  have : IsProbabilityMeasure (π.map x) := inferInstance
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real, ge_iff_le]
  calc _ ≤ ∫ _, (⨆ a, f a) ∂(π.map x) := integral_mono hf (integrable_const _) (fun a => le_ciSup hb a)
    _ = ⨆ a, f a := by simp


-- created on 2023-04-04
