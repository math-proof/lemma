/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/


import sympy.atlas.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift
import Lemma.Finset.Enumerative.Partition.MexPartitionCongruenceLift

namespace MetaMathlibExt

-- The first mex congruence specializes to `5n + 4` at `t = 1`.
example (hbase : ∀ n : ℕ, 5 ∣ Fintype.card (Nat.Partition (5 * n + 4))) :
    ∀ n : ℕ, 5 ∣ (@Finset.filter (Nat.Partition (5 * n + 4))
      (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % 5 = 5 % 5 ∧
        μ ∉ lam.parts ∧
        (∀ k : ℕ, 0 < k → k < μ → k % 5 = 5 % 5 → k ∈ lam.parts) ∧
        μ % (2 * 5) = 5 % (2 * 5))
      (Classical.decPred _) Finset.univ).card := by
  simpa using
    (mesh_partition_congruence_lift 5 5 4 (by decide) (by decide) (by decide)
      hbase 1 (by decide)).1

-- The second mex congruence specializes to `7n + 5` at `t = 2`.
example (hbase : ∀ n : ℕ, 7 ∣ Fintype.card (Nat.Partition (7 * n + 5))) :
    ∀ n : ℕ, 7 ∣ (@Finset.filter (Nat.Partition (7 * n + 5))
      (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % 28 = 14 % 28 ∧
        μ ∉ lam.parts ∧
        (∀ k : ℕ, 0 < k → k < μ → k % 28 = 14 % 28 → k ∈ lam.parts) ∧
        μ % 56 = 14 % 56)
      (Classical.decPred _) Finset.univ).card := by
  simpa using
    (mesh_partition_congruence_lift 7 7 5 (by decide) (by decide) (by decide)
      hbase 2 (by decide)).2

end MetaMathlibExt
