module

public import Class.Probability.Rv

public section

open MeasureTheory


/-- An a.e. measurable random variable whose law equals a reference density supplies the
`SinglePSpace π x` instance. -/
public theorem Random.SinglePSpace.of.AEMeasurable.Distributed
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
  {ρ : α → ENNReal}
-- given
  (hρ : Measurable ρ)
  (h : π.map x = μ.measure.withDensity ρ)
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
-- updated on 2026-11-17
