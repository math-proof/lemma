module

public import Mathlib
public import Structure.v1.Atlas.Probability.code.RegularConditionalDistribution

public section

open MeasureTheory ProbabilityTheory MeasureTheory.Measure


namespace ProbabilityTheory

/--
[condDistrib_isRegularConditionalDistribution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RegularConditionalDistribution.lean)
-/
public theorem condDistrib_isRegularConditionalDistribution
  [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  [Nonempty Ω]
  {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β}
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {X : α → β}
  {Y : α → Ω}
-- given
  (hX : Measurable X)
  (hY : Measurable Y) :
-- imply
  IsRegularConditionalDistribution (condDistrib Y X μ) Y X μ where
    isMarkovKernel := inferInstance
    ae_eq_condExp := fun hs => condDistrib_ae_eq_condExp hX hY hs
end ProbabilityTheory



-- created on 2026-10-23
