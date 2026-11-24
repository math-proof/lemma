module
public import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
public import Theorem.Finset.Enumerative.ULDMotzkinNumberOfRankR
public import Def.MathlibExtTest.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/
namespace MetaMathlibExt.ULDMotzkin

example : uldMotzkinNumber 1 ones 1 ones (by decide) 0 = 1 := by decide

example : uldMotzkinNumber 1 ones 1 ones (by decide) 2 = 2 := by decide

end MetaMathlibExt.ULDMotzkin
