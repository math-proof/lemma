/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MarkedStepInAMarkedDyckPath.lean -/
module

public import Def.Combinatorics.Enumerative.MarkedStepInAMarkedDyckPath.Part2
public import Theorem.Finset.Enumerative.MarkedStepInAMarkedDyckPath

public section

namespace MetaMathlibExt

open MarkedDyckStep

example : markedDyckCountE [E, Nstar, E, N] = 2 := by rfl

example : markedDyckCountN [E, Nstar, E, N] = 1 := by rfl

example : markedDyckCountNstar [E, Nstar, E, N] = 1 := by rfl

end MetaMathlibExt
