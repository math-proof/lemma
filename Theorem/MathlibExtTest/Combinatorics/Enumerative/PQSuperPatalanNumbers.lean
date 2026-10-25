/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQSuperPatalanNumbers.lean -/


import Mathlib.Tactic
import Def.Combinatorics.Enumerative.PQSuperPatalanNumbers
import Def.MathlibExtTest.Combinatorics.Enumerative.PQSuperPatalanNumbers


namespace MetaMathlibExt

example : pqSuperPatalanNumber binaryPatalanParams 0 0 = 1 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

example : pqSuperPatalanNumber binaryPatalanParams 1 0 = 2 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

end MetaMathlibExt
