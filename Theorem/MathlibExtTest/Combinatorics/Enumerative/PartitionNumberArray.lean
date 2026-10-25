/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PartitionNumberArray.lean -/


import Def.Combinatorics.Enumerative.PartitionNumberArray.Part2
import Def.MathlibExtTest.Combinatorics.Enumerative.PartitionNumberArray


namespace MetaMathlibExt.PartitionNumberArray

example : genStirlingSecond ⟨2, by decide⟩ 3 1 = 6 := by decide

example : M3 sourcePartition = 10 := by decide

example : M32 ⟨2, by decide⟩ sourcePartition = 20 := by decide

example : M31 ⟨2, by decide⟩ sourcePartition = 20 := by decide

end MetaMathlibExt.PartitionNumberArray
