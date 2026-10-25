/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/ModifiedBesselFirstKind.lean -/


import Def.Analysis.SpecialFunctions.ModifiedBesselFirstKind
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt

example (x : ℝ) : modifiedBesselI_zero x = modifiedBesselI 0 x := rfl

example (x : ℝ) : modifiedBesselI_term 0 0 x = 1 := by
  norm_num [modifiedBesselI_term]

example (x : ℝ) : modifiedBesselI_term 1 0 x = x / 2 := by
  norm_num [modifiedBesselI_term]

end MetaMathlibExt
