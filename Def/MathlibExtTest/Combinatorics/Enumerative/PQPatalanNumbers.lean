/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQPatalanNumbers.lean -/


module

public import Mathlib.Tactic.NormNum
public import Def.Combinatorics.Enumerative.PQPatalanNumbers.Part2

@[expose] public section

namespace MetaMathlibExt

def catalanPatalanParams : PQPatalanParams where
  p := 2
  q := 1
  hp := by decide
  hq_pos := by decide
  hq := by decide

end MetaMathlibExt
