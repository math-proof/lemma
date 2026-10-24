/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/


import sympy.atlas.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath
import Lemma.Finset.Enumerative.MarkedStepInAMultiMarkedDyckPath

namespace MetaMathlibExt

example : multiMarkedIsVert MultiMarkedStep.E = false := rfl
example :
    multiMarkedCountMarkedT
      [MultiMarkedStep.marked 2 (by decide), MultiMarkedStep.N] 2 = 1 :=
  rfl
example : multiMarkedShiftedIndexSum [MultiMarkedStep.marked 4 (by decide)] = 3 := rfl

private def sourceExampleSteps : List MultiMarkedStep :=
  [.E, .N, .E, .E, .marked 4 (by omega), .marked 2 (by omega),
    .E, .N, .E, .marked 3 (by omega), .E, .N]

private def sourceExamplePath : MultiMarkedDyckPath where
  steps := sourceExampleSteps
  underdiagonal := by
    intro k hk
    have hk' : k ≤ 12 := by simpa [sourceExampleSteps] using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  diagonal_endpoint := by decide

example : multiMarkedSize sourceExamplePath.steps = 12 := by decide

example : MultiMarkedUnmarkedTail 12 :=
  ⟨sourceExamplePath, by decide, sourceExamplePath_unmarkedTail⟩

example : multiMarkedCountPlainN sourceExamplePath.steps +
    multiMarkedIndexSum sourceExamplePath.steps = 12 := by
  rw [← multiMarkedSizeEq sourceExamplePath]
  decide

end MetaMathlibExt
