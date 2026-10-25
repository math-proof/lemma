/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/


import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
import Lemma.Finset.Enumerative.ULDMotzkinNumberOfRankR
import Def.MathlibExtTest.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR


namespace MetaMathlibExt.ULDMotzkin

example : uldMotzkinNumber 1 ones 1 ones (by decide) 0 = 1 := by decide

example : uldMotzkinNumber 1 ones 1 ones (by decide) 2 = 2 := by decide

end MetaMathlibExt.ULDMotzkin
