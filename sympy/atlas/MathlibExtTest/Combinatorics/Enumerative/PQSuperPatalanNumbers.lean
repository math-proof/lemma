/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQSuperPatalanNumbers.lean -/


import Mathlib.Tactic
import sympy.atlas.Combinatorics.Enumerative.PQSuperPatalanNumbers

namespace MetaMathlibExt

private def binaryPatalanParams : PQPatalanParams where
  p := 2
  q := 1
  hp := by omega
  hq_pos := by omega
  hq := by omega

example : pqSuperPatalanNumber binaryPatalanParams 0 0 = 1 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

example : pqSuperPatalanNumber binaryPatalanParams 1 0 = 2 := by
  norm_num [pqSuperPatalanNumber, patalanGeneralizedBinomial, binaryPatalanParams]

end MetaMathlibExt
