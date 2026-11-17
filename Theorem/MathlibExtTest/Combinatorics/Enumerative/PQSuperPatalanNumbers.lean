/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQSuperPatalanNumbers.lean -/
module

public import Mathlib.Tactic
public import Def.Combinatorics.Enumerative.PQSuperPatalanNumbers
public import Def.MathlibExtTest.Combinatorics.Enumerative.PQSuperPatalanNumbers

public section

namespace MetaMathlibExt

example : pqSuperPatalanNumber binaryPatalanParams 0 0 = 1 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

example : pqSuperPatalanNumber binaryPatalanParams 1 0 = 2 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

end MetaMathlibExt
