import Mathlib.Probability.HasLaw
import Lemma.Random.Map.eq.WithDensityProb
open Random MeasureTheory ProbabilityTheory


/--
`HasLaw x (withDensity ρ) π` is equivalent to the canonical density of `x` being a.e. equal to `ρ`
(`π.prob x =ᵐ[ReferenceMeasure.measure] ρ`), under `SinglePSpace`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω} {x : Ω → α} [SinglePSpace π x]
  {ρ : α → ENNReal}
-- given
  (hρ : Measurable ρ) :
-- imply
  HasLaw x (ReferenceMeasure.measure.withDensity ρ) π ↔
      π.prob x =ᵐ[ReferenceMeasure.measure] ρ := by
-- proof
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  ·
    have hmap : π.map x = ReferenceMeasure.measure.withDensity ρ := h.map_eq
    show (π.map x).rnDeriv ReferenceMeasure.measure =ᵐ[ReferenceMeasure.measure] ρ
    rw [hmap]
    exact Measure.rnDeriv_withDensity _ hρ
  · exact {
      aemeasurable := (inferInstance : SinglePSpace π x).aemeasurable
      map_eq := (@Map.eq.WithDensityProb Ω α _ _ π x _).trans (withDensity_congr_ae h)
    }


-- created on 2026-10-07
-- updated on 2026-10-29
