/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/FortunateNumber.lean -/
module

public import Mathlib.Tactic
public import Def.Combinatorics.Enumerative.FortunateNumber

public section

namespace MetaMathlibExt

example : IsFortunateNumber 3 5 := by
  have hprim : primorial 3 = 6 := by decide
  rw [IsFortunateNumber, hprim]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro k hk1 hk5
  interval_cases k <;> norm_num

example : ¬ IsFortunateNumber 3 2 := by
  have hprim : primorial 3 = 6 := by decide
  rw [IsFortunateNumber, hprim]
  norm_num

end MetaMathlibExt
