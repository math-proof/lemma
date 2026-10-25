/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/LambertSeries.lean -/


import Mathlib.Tactic.NormNum
import Def.Analysis.SpecialFunctions.LambertSeries


namespace MetaMathlibExt

noncomputable def zeroInUnitDisk : {q : ℂ // ‖q‖ < 1} :=
  ⟨0, by norm_num⟩

end MetaMathlibExt
