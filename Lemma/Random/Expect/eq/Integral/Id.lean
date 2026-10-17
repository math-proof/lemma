import sympy.stats.joint_rv
import sympy.Basic
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
open MeasureTheory


/--
Expectation.ofRV of the identity equals the Bochner integral of the RV.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x : Ω → ℝ} [PSpace π x] :
-- imply
  Expectation.ofRV π x (fun a : ℝ ↦ a) = ∫ ω, x ω ∂π := by
-- proof
  apply Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
  apply measurable_id.aestronglyMeasurable


-- created on 2026-10-17
