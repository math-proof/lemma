import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
open Random MeasureTheory


/--
Bayes formula for probability densities (the continuous analogue of the event formula
`Pr(x | y) = Pr(x, y) / Pr(y)`): the conditional density of `x` given `y` equals the joint
density `Pr(x, y)` divided by the marginal density `Pr(y)`.

The identity holds almost everywhere with respect to the product of the reference measures;
point values on the null set where the marginal density vanishes (and Radon–Nikodym
derivatives in general) carry no probabilistic information. The same statement covers
discrete random variables by taking the counting measure as the reference measure, where
the `lintegral` reduces to a sum. The marginal `Pr(y)` is obtained from the joint
`PSpace ℙ (x, y)` via `PSpace.of.PSpace_Joint.snd`.
-/
@[main]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {ℙ : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace ℙ (x, y)) :
-- imply
  have := PSpace.of.PSpace_Joint.snd hP
  ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure,
    ℙ.condProb (x, y) («x.bvar», «y.bvar») =
      ℙ.prob (x, y) («x.bvar», «y.bvar») / ℙ.prob y «y.bvar» := by
-- proof
  have := PSpace.of.PSpace_Joint.snd hP
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  have hmapy : ℙ.map (fun ω ↦ ((x, y) ω).2) = ℙ.map y := by congr
  have hae : (fun z : α × β ↦ ℙ.condProb (x, y) z) =ᵐ[μ.prod ν]
      (fun z ↦ ℙ.prob (x, y) z / ℙ.prob y z.2) := by
    filter_upwards with z
    unfold Measure.condProb Measure.prob
    rw [hmapy]
  exact Measure.ae_ae_of_ae_prod hae


-- created on 2020-12-09
-- updated on 2026-09-14
