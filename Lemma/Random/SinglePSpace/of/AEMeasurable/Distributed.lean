import Def.Probability.SymbolicProbability.Part2
import Initialize.Tactic.Attr.Basic
open MeasureTheory


/-- An a.e. measurable random variable whose law equals a reference density supplies the
`SinglePSpace π x` instance. -/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
  {ρ : α → ENNReal}
-- given
  (hρ : Measurable ρ)
  (h : π.map x = ReferenceMeasure.measure.withDensity ρ)
  (hx : AEMeasurable x π) :
-- imply
  SinglePSpace π x := by
-- proof
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨ρ, hρ, h⟩
  }


-- created on 2026-10-07
-- updated on 2026-10-29
