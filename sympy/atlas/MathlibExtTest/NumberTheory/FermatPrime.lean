/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FermatPrime.lean -/


import sympy.atlas.NumberTheory.FermatPrime
import Mathlib.Tactic.NormNum.Prime

namespace MetaMathlibExt

example : IsFermatPrime 3 := by
  refine ⟨by norm_num, 0, ?_⟩
  rfl

example : IsFermatPrime 5 := by
  refine ⟨by norm_num, 1, ?_⟩
  rfl

end MetaMathlibExt
