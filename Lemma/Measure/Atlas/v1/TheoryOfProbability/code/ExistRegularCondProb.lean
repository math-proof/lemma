import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.ExistRegularCondProb
open MeasureTheory ProbabilityTheory


namespace ProbabilityTheory

/--
[exists_regularConditionalDistribution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ExistRegularCondProb.lean)
-/
@[path]
lemma exists_regularConditionalDistribution
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
  ∃ κ : Kernel β Ω, IsRegularConditionalDistribution κ Y X μ :=
-- proof
  ⟨condDistrib Y X μ, condDistrib_isRegularConditionalDistribution hX hY⟩
end ProbabilityTheory



-- created on 2026-10-23
