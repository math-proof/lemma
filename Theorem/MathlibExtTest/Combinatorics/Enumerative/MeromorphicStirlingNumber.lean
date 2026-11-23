/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MeromorphicStirlingNumber.lean -/
module

public import Mathlib.Tactic.NormNum
public import Def.Combinatorics.Enumerative.MeromorphicStirlingNumber
public import Theorem.Finset.Enumerative.MeromorphicStirlingNumber

public section

namespace MetaMathlibExt

example : meromorphicStirlingFirst 3 2 = -3 := by
  norm_num [meromorphicStirlingFirst, Nat.factorial]

example : besselNumberFirst 3 2 = -3 := by
  norm_num [besselNumberFirst, Nat.factorial]

example : meromorphicStirlingSecond 3 2 = 3 := by
  norm_num [meromorphicStirlingSecond, Nat.factorial]

example : besselNumberSecond 3 2 = 3 := by
  norm_num [besselNumberSecond, Nat.factorial]

end MetaMathlibExt
