/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/JosephusFunction.lean -/
module

public import Def.Combinatorics.Enumerative.JosephusFunction
public import Theorem.Finset.Enumerative.JosephusFunction

public section

namespace MetaMathlibExt

example : josephus 2 5 = 3 := by decide

example : josephus 3 5 = 4 := by decide

example : 1 ≤ josephus 8 3 ∧ josephus 8 3 ≤ 3 := by decide

end MetaMathlibExt
