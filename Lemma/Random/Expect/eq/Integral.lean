import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
open MeasureTheory Random


/--
`𝔼[x: π](x)` equals the Bochner integral of the random variable.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x : Ω → ℝ} [PSpace π x] :
-- imply
  𝔼[x: π](x) = ∫ ω, x ω ∂π := by
-- proof
  change Expectation.ofRV π x (fun a : ℝ ↦ a) = _
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
  apply measurable_id.aestronglyMeasurable


-- created on 2026-10-17
-- updated on 2026-11-03
