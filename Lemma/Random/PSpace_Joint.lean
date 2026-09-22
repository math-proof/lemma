import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma Comm
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  PSpace π (y, x) := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  obtain ⟨p, D, hjoint⟩ := hP.exists_distribution
  let p' : β × α → ENNReal := p ∘ Prod.swap
  have hp' : Measurable p' := D.measurable_density.comp measurable_swap
  have hmap : π.map (y, x) = Measure.map Prod.swap (π.map (x, y)) :=
    (AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable
      hP.aemeasurable).symm
  have hwd :
      Measure.map Prod.swap ((μ.prod ν).withDensity p) =
        (Measure.map Prod.swap (μ.prod ν)).withDensity p' := by
    ext s hs
    simp only [Measure.map_apply measurable_swap hs,
      withDensity_apply _ (measurable_swap hs), withDensity_apply _ hs,
      setLIntegral_map hs hp' measurable_swap]
    congr
  have hlaw : π.map (y, x) = (ν.prod μ).withDensity p' := by
    rw [hmap, hjoint]
    show Measure.map Prod.swap ((μ.prod ν).withDensity p) = _
    rw [hwd, Measure.prod_swap]
  exact {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := measurable_swap.comp_aemeasurable hP.aemeasurable
    exists_distribution := ⟨p', ⟨hp'⟩, hlaw⟩
  }


-- created on 2026-09-22
