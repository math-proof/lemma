/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/


import Def.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath.Part2
import Lemma.Finset.Enumerative.MarkedStepInAMultiMarkedDyckPath
import Theorem.MathlibExtTest.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath


namespace MetaMathlibExt

def sourceExampleSteps : List MultiMarkedStep :=
  [.E, .N, .E, .E, .marked 4 (by omega), .marked 2 (by omega),
    .E, .N, .E, .marked 3 (by omega), .E, .N]

def sourceExamplePath : MultiMarkedDyckPath where
  steps := sourceExampleSteps
  underdiagonal := by
    intro k hk
    have hk' : k ≤ 12 := by simpa [sourceExampleSteps] using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  diagonal_endpoint := by decide

end MetaMathlibExt
