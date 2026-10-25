/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQSuperPatalanNumbers.lean -/


import Mathlib.Tactic
import Def.Combinatorics.Enumerative.PQSuperPatalanNumbers


namespace MetaMathlibExt

def binaryPatalanParams : PQPatalanParams where
  p := 2
  q := 1
  hp := by omega
  hq_pos := by omega
  hq := by omega

end MetaMathlibExt
