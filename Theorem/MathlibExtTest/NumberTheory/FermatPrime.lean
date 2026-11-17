/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FermatPrime.lean -/
module

public import Def.NumberTheory.FermatPrime
public import Mathlib.Tactic.NormNum.Prime

public section

namespace MetaMathlibExt

example : IsFermatPrime 3 := by
  refine ⟨by norm_num, 0, ?_⟩
  rfl

example : IsFermatPrime 5 := by
  refine ⟨by norm_num, 1, ?_⟩
  rfl

end MetaMathlibExt
