module

public import Mathlib
public import Def.Probability.CharacteristicFunction

public section

open MeasureTheory Complex ProbabilityTheory


namespace ProbabilityTheory

/--
[charFun_eq_measureTheory_charFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CharacteristicFunction.lean)
-/
public theorem charFun_eq_measureTheory_charFun
  {μ : Measure ℝ}
  {t : ℝ} :
-- imply
  charFun μ t = MeasureTheory.charFun μ t := by
-- proof
  simp only [charFun, MeasureTheory.charFun_apply_real]
  congr 1 with x
  ring_nf

end ProbabilityTheory


-- created on 2026-10-23
