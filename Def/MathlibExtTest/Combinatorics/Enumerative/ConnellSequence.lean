/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ConnellSequence.lean -/


module

public import Def.Combinatorics.Enumerative.ConnellSequence.Part2

@[expose] public section

namespace MetaMathlibExt

def connellTwoOne : ConnellParameters :=
  { m := 2, r := 1, two_le_m := by decide, pos_r := by decide }

def connellFiveThree : ConnellParameters :=
  { m := 5, r := 3, two_le_m := by decide, pos_r := by decide }

end MetaMathlibExt
