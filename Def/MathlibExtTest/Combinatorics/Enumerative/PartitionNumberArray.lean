/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PartitionNumberArray.lean -/


import Def.Combinatorics.Enumerative.PartitionNumberArray.Part2


namespace MetaMathlibExt.PartitionNumberArray

def sourcePartition : PartitionMultiplicity 5 where
  vec := fun i => if i.val = 0 then 3 else if i.val = 1 then 1 else 0
  weighted := by decide

end MetaMathlibExt.PartitionNumberArray
