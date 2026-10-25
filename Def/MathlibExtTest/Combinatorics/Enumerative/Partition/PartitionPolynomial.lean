/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean -/


import Def.Combinatorics.Enumerative.Partition.PartitionPolynomial
import Lemma.Finset.Enumerative.Partition.PartitionPolynomial


namespace MetaMathlibExt

def samplePartition : Nat.Partition 10 :=
  Nat.Partition.ofMultiset {1, 2, 2, 5}

end MetaMathlibExt
