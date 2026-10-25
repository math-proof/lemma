/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQPatalanNumbers.lean -/


import Mathlib.Tactic.NormNum
import Def.Combinatorics.Enumerative.PQPatalanNumbers.Part2


namespace MetaMathlibExt

def catalanPatalanParams : PQPatalanParams where
  p := 2
  q := 1
  hp := by decide
  hq_pos := by decide
  hq := by decide

end MetaMathlibExt
