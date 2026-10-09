import sympy.stats.symbolic_probability
import sympy.Basic
open MeasureTheory


/-- An `x ~ D` hypothesis, together with an a.e. measurability proof for `x`, supplies the
`SinglePSpace D.measure x` instance. -/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
  {ρ : α → ENNReal}
  {D : Distribution π ρ}
-- given
  (h : x ~ D)
  (hx : AEMeasurable x π) :
-- imply
  SinglePSpace π x := by
-- proof
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨D.density, D, h⟩
  }


-- created on 2026-10-07
