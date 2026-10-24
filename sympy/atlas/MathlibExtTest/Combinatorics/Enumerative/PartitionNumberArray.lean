/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PartitionNumberArray.lean -/


import sympy.atlas.Combinatorics.Enumerative.PartitionNumberArray

namespace MetaMathlibExt.PartitionNumberArray

private def sourcePartition : PartitionMultiplicity 5 where
  vec := fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else 0
  weighted := by decide

example : genStirlingSecond ⟨2, by decide⟩ 3 1 = 6 := by decide
example : M3 sourcePartition = 10 := by decide
example : M32 ⟨2, by decide⟩ sourcePartition = 20 := by decide
example : M31 ⟨2, by decide⟩ sourcePartition = 20 := by decide

end MetaMathlibExt.PartitionNumberArray
