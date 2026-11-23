/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/
module

public import Def.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath.Part2
public import Theorem.Finset.Enumerative.MarkedStepInAMultiMarkedDyckPath

public section

namespace MetaMathlibExt

example : multiMarkedIsVert MultiMarkedStep.E = false := rfl

example :
    multiMarkedCountMarkedT
      [MultiMarkedStep.marked 2 (by decide), MultiMarkedStep.N] 2 = 1 :=
  rfl

example : multiMarkedShiftedIndexSum [MultiMarkedStep.marked 4 (by decide)] = 3 := rfl

end MetaMathlibExt
