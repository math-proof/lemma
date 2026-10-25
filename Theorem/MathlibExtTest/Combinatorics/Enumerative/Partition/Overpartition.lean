/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/Overpartition.lean -/


import Def.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition


namespace Nat.Overpartition

example : Nat.Overpartition 0 :=
  ofPartition (Nat.Partition.ofMultiset (∅ : Multiset ℕ))

end Nat.Overpartition
