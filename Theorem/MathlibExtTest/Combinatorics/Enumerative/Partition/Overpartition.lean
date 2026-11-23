/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/Overpartition.lean -/
module

public import Def.Combinatorics.Enumerative.Partition.Overpartition
public import Theorem.Nat.Enumerative.Partition.Overpartition

public section

namespace Nat.Overpartition

example : Nat.Overpartition 0 :=
  ofPartition (Nat.Partition.ofMultiset (∅ : Multiset ℕ))

end Nat.Overpartition
