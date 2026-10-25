/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/AndrewsMacMahonPartition.lean -/


import Lemma.Finset.Enumerative.Partition.AndrewsMacMahonPartition


namespace MetaMathlibExt

-- MacMahon's case at `n = 6` follows by specializing Andrews' theorem to `r = 1`.
example (r n : ℕ) (hr : r = 1) (hn : n = 6) :
    Set.ncard { p : Nat.Partition n |
      ∀ m ∈ p.parts, Odd (p.parts.count m) → 2 * r + 1 ≤ p.parts.count m } =
    Set.ncard { p : Nat.Partition n |
      ∀ m ∈ p.parts, Odd m → m % (4 * r + 2) = 2 * r + 1 } := by
  subst r
  subst n
  exact andrews_macmahon_partition_identity 1 6

end MetaMathlibExt
