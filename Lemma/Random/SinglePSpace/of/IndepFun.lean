import sympy.stats.joint_rv
import sympy.Basic
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.Map.eq.WithDensityProb
open Random MeasureTheory
open scoped ProbabilityTheory


/--
Two random variables whose laws each admit a density (`SinglePSpace π x` and
`SinglePSpace π y`) also span a **joint** probability space with density when they are
independent: by `IndepFun`, the joint law is the product of the marginal laws, and the
product of two measures with densities `px`, `py` is the product measure with density
`fun z ↦ px z.1 * py z.2`. The a.e. measurability of `x` and `y` needed by `IndepFun` is
read off the `SinglePSpace` instances (which package `AEMeasurable`); plain `Measurable`
hypotheses are not required. The converse is false without independence — two ac
marginals can have a singular joint law (e.g. `y = x` over a Lebesgue state space).
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → β} [SinglePSpace π x] [SinglePSpace π y]
-- given
  (hxy : ProbabilityTheory.IndepFun x y π) :
-- imply
  SinglePSpace π (x, y) := by
-- proof
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let px := π.prob x
  let py := π.prob y
  let p : α × β → ENNReal := fun z ↦ px z.1 * py z.2
  have hpx : Measurable px := Measure.measurable_rnDeriv _ _
  have hpy : Measurable py := Measure.measurable_rnDeriv _ _
  have hp : Measurable p :=
    (hpx.comp measurable_fst).mul (hpy.comp measurable_snd)
  have haex : AEMeasurable x π := PSpace.aemeasurable
  have haey : AEMeasurable y π := PSpace.aemeasurable
  have hindep : π.map (x, y) = (π.map x).prod (π.map y) :=
    ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map haex haey hxy
  apply SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable (haex.prodMk haey) hp
  rw [hindep, Map.eq.WithDensityProb,
    Map.eq.WithDensityProb, prod_withDensity hpx hpy]


-- created on 2026-10-07
