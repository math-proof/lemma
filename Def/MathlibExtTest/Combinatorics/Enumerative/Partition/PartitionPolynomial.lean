/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean -/

module

public import Def.Combinatorics.Enumerative.Partition.PartitionPolynomial
public import Theorem.Finset.Enumerative.Partition.PartitionPolynomial

@[expose] public section

namespace MetaMathlibExt

def samplePartition : Nat.Partition 10 :=
  Nat.Partition.ofMultiset {1, 2, 2, 5}

end MetaMathlibExt
