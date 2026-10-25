/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean -/


import Def.Combinatorics.Enumerative.Partition.PartitionPolynomial
import Lemma.Finset.Enumerative.Partition.PartitionPolynomial
import Def.MathlibExtTest.Combinatorics.Enumerative.Partition.PartitionPolynomial


namespace MetaMathlibExt

example : partitionPolynomial (Nat.Partition.indiscrete 0) = 0 := by
  simp [partitionPolynomial]

example : (partitionPolynomial samplePartition).coeff 2 = 2 := by
  rw [coeff_partitionPolynomial]
  decide

example : (partitionPolynomial samplePartition).coeff 3 = 0 := by
  rw [coeff_partitionPolynomial]
  decide

example : (partitionPolynomial samplePartition).eval 1 = 4 := by
  rw [eval_partitionPolynomial_at_one]
  decide

#print axioms partitionPolynomial
#print axioms coeff_partitionPolynomial
#print axioms eval_partitionPolynomial_at_one

end MetaMathlibExt
