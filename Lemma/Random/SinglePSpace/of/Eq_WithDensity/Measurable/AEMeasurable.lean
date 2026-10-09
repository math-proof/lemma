import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory
open scoped ProbabilityTheory


/--
Build a joint `SinglePSpace π (x, y)` from an explicit density `p` of the joint law: if
`π.map (x, y)` equals the product reference measure with density `p`, then `(x, y)` admits
`p` as its distribution. The a.e. measurability of the pair is supplied directly.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
  {y : Ω → β}
  {p : α × β → ENNReal}
-- given
  (hxy : AEMeasurable (x, y) π)
  (hp : Measurable p)
  (hjoint : π.map (x, y) = (ReferenceMeasure.measure.prod ReferenceMeasure.measure).withDensity p) :
-- imply
  SinglePSpace π (x, y) := by
-- proof
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hxy
    exists_distribution := ⟨p, ⟨hp⟩, hjoint⟩
  }


-- created on 2026-10-07
