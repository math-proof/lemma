import Mathlib
import sympy.Basic
import Structure.v1.Atlas.TheoryOfProbability.code.RegularConditionalDistribution
open MeasureTheory ProbabilityTheory MeasureTheory.Measure


namespace ProbabilityTheory

/--
[condDistrib_isRegularConditionalDistribution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RegularConditionalDistribution.lean)
-/
@[path]
lemma condDistrib_isRegularConditionalDistribution
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
  IsRegularConditionalDistribution (condDistrib Y X μ) Y X μ where isMarkovKernel :=
-- proof
  inferInstance
    ae_eq_condExp hs := condDistrib_ae_eq_condExp hX hY hs
end ProbabilityTheory



-- created on 2026-10-23
