import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
Change of variables: Expectation.ofRV of an observable equals the Bochner integral of the composition.
-/
@[path]
private lemma main
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] [MeasurableSpace α]
  {π : Measure Ω} {x : Ω → α} [PSpace π x] {f : α → E}
-- given
  (hf : AEStronglyMeasurable f (π.map x)) :
-- imply
  Expectation.ofRV π x f = ∫ ω, f (x ω) ∂π := by
-- proof
  simp only [Expectation.ofRV]
  apply integral_map PSpace.aemeasurable hf


-- created on 2026-10-17
