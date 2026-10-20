import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.AndrewsMacMahonPartition
open PowerSeries
open scoped PowerSeries.WithPiTopology
open MetaMathlibExt


/--
[andrews_macmahon_partition_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/AndrewsMacMahonPartition.lean)
-/
@[path]
private lemma andrews_macmahon_partition_identity_eq
  {r n : ℕ} :
-- imply
  Set.ncard { p : Nat.Partition n |
    ∀ m ∈ p.parts, Odd (p.parts.count m) → 2 * r + 1 ≤ p.parts.count m } =
    Set.ncard { p : Nat.Partition n |
    ∀ m ∈ p.parts, Odd m → m % (4 * r + 2) = 2 * r + 1 } := by
-- proof
  apply MetaMathlibExt.andrews_macmahon_partition_identity r n


-- created on 2026-10-20
