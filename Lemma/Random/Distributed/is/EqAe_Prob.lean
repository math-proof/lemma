import sympy.stats.symbolic_probability
import sympy.Basic
import Lemma.Random.Map.eq.WithDensityProb
open Random MeasureTheory


/--
`x ~ D` is equivalent to the canonical density of `x` being a.e. equal to `D`'s density
(`π.prob x =ᵐ[ReferenceMeasure.measure] ρ`).
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω} {x : Ω → α} [SinglePSpace π x]
  {ρ : α → ENNReal}
-- given
  (D : Distribution π ρ) :
-- imply
  x ~ D ↔ π.prob x =ᵐ[ReferenceMeasure.measure] ρ := by
-- proof
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  ·
    have h : D.measure.map x =
        ReferenceMeasure.measure.withDensity D.density := h
    show (D.measure.map x).rnDeriv ReferenceMeasure.measure =ᵐ[ReferenceMeasure.measure] D.density
    rw [h]
    exact Measure.rnDeriv_withDensity _ D.measurable_density
  · exact (@Map.eq.WithDensityProb Ω α _ _ π x _).trans (withDensity_congr_ae h)


-- created on 2026-10-07
