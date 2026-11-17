/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/LambertSeries.lean -/


module

public import Mathlib.Tactic.NormNum
public import Def.Analysis.SpecialFunctions.LambertSeries

@[expose] public section

namespace MetaMathlibExt

noncomputable def zeroInUnitDisk : {q : ℂ // ‖q‖ < 1} :=
  ⟨0, by norm_num⟩

end MetaMathlibExt
