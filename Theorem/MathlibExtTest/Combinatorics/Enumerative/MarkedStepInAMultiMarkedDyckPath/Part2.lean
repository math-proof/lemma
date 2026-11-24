module
public import Def.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath.Part2
public import Theorem.Finset.Enumerative.MarkedStepInAMultiMarkedDyckPath
public import Def.MathlibExtTest.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/
namespace MetaMathlibExt

example : multiMarkedSize sourceExamplePath.steps = 12 := by decide

example : MultiMarkedUnmarkedTail 12 :=
  ⟨sourceExamplePath, by decide, sourceExamplePath_unmarkedTail⟩

example : multiMarkedCountPlainN sourceExamplePath.steps +
    multiMarkedIndexSum sourceExamplePath.steps = 12 := by
  rw [← multiMarkedSizeEq sourceExamplePath]
  decide

end MetaMathlibExt
