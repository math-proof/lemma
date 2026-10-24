/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PentagonalNumber.lean -/


import sympy.atlas.Combinatorics.Enumerative.PentagonalNumber
import Lemma.Finset.Enumerative.PentagonalNumber

namespace MetaMathlibExt

example : partitionFunction 0 = 1 := by simp

example : partitionFunction 1 = 1 := by simp

example (n : ℕ) : partitionFunction n = Fintype.card (Nat.Partition n) := rfl

end MetaMathlibExt
