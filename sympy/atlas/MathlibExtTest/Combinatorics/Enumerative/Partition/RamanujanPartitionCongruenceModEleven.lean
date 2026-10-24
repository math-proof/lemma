/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean -/


import sympy.atlas.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
import Lemma.Finset.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
import Lemma.Finset.Enumerative.Partition.RamanujanPartitionCongruence
import sympy.atlas.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence


namespace MathlibExtTest.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven

-- The modulo-11 theorem gives the first nontrivial congruence at `m = 1`.
example : 11 ∣ Fintype.card (Nat.Partition 17) := by
  have h := MetaMathlibExt.ramanujan_partition_congruence_mod_eleven 1
  rw [Nat.modEq_zero_iff_dvd] at h
  simpa using h

-- The triangular identity specializes the general coefficient-to-partition transfer.
example (t : ℕ)
    (hcoeff : ∀ n : ℕ, (7 : ℤ) ∣ PowerSeries.coeff (7 * n + 5)
      (PowerSeries.pentagonalSeries ℤ ^ (7 - 1))) :
    7 ∣ Fintype.card (Nat.Partition (7 * (2 * (t + 1).choose 2) + 5)) := by
  rw [MetaMathlibExt.two_mul_choose_two_succ]
  have hfact : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  exact @MetaMathlibExt.dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow
    7 5 hfact (by decide) hcoeff (t * (t + 1))

end MathlibExtTest.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
