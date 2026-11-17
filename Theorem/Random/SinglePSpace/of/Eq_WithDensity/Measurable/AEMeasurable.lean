module

public import Class.Probability.Rv
public import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

public noncomputable section

/-- Product of two reference measures, used to view a pair of random variables as a single
joint random variable on the product type. -/
public noncomputable instance instReferenceMeasureProd [ReferenceMeasure α] [ReferenceMeasure β] :
    ReferenceMeasure (α × β) where
  toMeasurableSpace := inferInstance
  measure := ReferenceMeasure.measure.prod ReferenceMeasure.measure
  toSigmaFinite := inferInstance

/--
Build a joint SinglePSpace of the pair (x, y) from an explicit density p of the joint law:
if the pushforward of π along the pair map equals the product reference measure with
density p, then the pair admits p as its distribution. The a.e. measurability of the
pair is supplied directly.
-/
public theorem Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α]
  [ν : ReferenceMeasure β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
  {y : Ω → β}
  {p : α × β → ENNReal}
-- given
  (hxy : AEMeasurable (fun ω => (x ω, y ω)) π)
  (hp : Measurable p)
  (hjoint : π.map (fun ω => (x ω, y ω)) = (μ.measure.prod ν.measure).withDensity p) :
-- imply
  SinglePSpace π (fun ω => (x ω, y ω)) := by
-- proof
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hxy
    exists_distribution := ⟨p, hp, hjoint⟩
  }


-- created on 2026-10-07
-- updated on 2026-11-17
