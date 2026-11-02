import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
open Random MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : SinglePSpace π (x, y)) :
-- imply
  have := SinglePSpace.of.SinglePSpace.snd hP
  ∀ᵐ «\sf{x}» ∂ReferenceMeasure.measure, ∀ᵐ «\sf{y}» ∂ReferenceMeasure.measure,
    ℙ[π](x = «\sf{x}» | y = «\sf{y}») =
      ℙ[π](x = «\sf{x}» ∧ y = «\sf{y}») / ℙ[π](y = «\sf{y}») := by
-- proof
  have := SinglePSpace.of.SinglePSpace.snd hP
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  have hmapy : π.map (fun ω ↦ ((x, y) ω).2) = π.map y := by congr
  have hae : (fun z : α × β ↦ π.condProb (x, y) z) =ᵐ[μ.prod ν]
      (fun z ↦ π.prob (x, y) z / π.prob y z.2) := by
    filter_upwards with z
    unfold Measure.condProb Measure.prob
    rw [hmapy]
  exact Measure.ae_ae_of_ae_prod hae


-- created on 2020-12-09
-- updated on 2026-11-02
