/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQSuperPatalanNumbers.lean -/


module

public import Mathlib.Tactic
public import Def.Combinatorics.Enumerative.PQSuperPatalanNumbers

@[expose] public section

namespace MetaMathlibExt

def binaryPatalanParams : PQPatalanParams where
  p := 2
  q := 1
  hp := by omega
  hq_pos := by omega
  hq := by omega

end MetaMathlibExt
