import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.CharacteristicFunction
open MeasureTheory Complex ProbabilityTheory


namespace ProbabilityTheory

/--
[charFun_eq_measureTheory_charFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CharacteristicFunction.lean)
-/
@[path]
lemma charFun_eq_measureTheory_charFun
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
