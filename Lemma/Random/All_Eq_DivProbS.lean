import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
open Random MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y)) :
-- imply
  have := PSpace.of.PSpace_Joint.snd hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
    ℙ[π](x = «x.bvar» | y = «y.bvar») =
      ℙ[π](x = «x.bvar» ∧ y = «y.bvar») / ℙ[π](y = «y.bvar») := by
-- proof
  have := PSpace.of.PSpace_Joint.snd hP
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
-- updated on 2026-09-20
