/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PalindromicNarayanaNumber.lean -/
module

public import Def.Combinatorics.Enumerative.PalindromicNarayanaNumber
public import Mathlib.Tactic.NormNum

public section

namespace MetaMathlibExt

example : palindromicNarayanaNumber 0 0 = 1 := by
  norm_num [palindromicNarayanaNumber]

example : palindromicNarayanaNumber 3 0 = 1 ∧
    palindromicNarayanaNumber 3 1 = 6 ∧
    palindromicNarayanaNumber 3 2 = 6 ∧
    palindromicNarayanaNumber 3 3 = 1 := by
  norm_num [palindromicNarayanaNumber, Nat.choose]

example : palindromicNarayanaNumber 3 4 = 0 := by
  norm_num [palindromicNarayanaNumber]

#print axioms palindromicNarayanaNumber

end MetaMathlibExt
