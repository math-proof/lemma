import Syntax.Probability.JointRv.Part6
import Initialize.Tactic.Attr.Basic
open MeasureTheory


/--
An expectation indexed by a coordinate is the integral of the observable against the law of that coordinate.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α]
  {π : Measure Ω}
  {x : Ω → α}
  {f : α → ℝ}
-- given
  [PSpace π x]
  (_ : AEStronglyMeasurable f (π.map x)) :
-- imply
  Expectation.ofRV π x f = ∫ a, f a ∂(π.map x) := by
-- proof
  simp only [Expectation.ofRV, expectation_real]


-- created on 2023-04-24
-- updated on 2026-10-26
