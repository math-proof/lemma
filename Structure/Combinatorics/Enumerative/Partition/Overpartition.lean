/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
/-!
# Overpartitions

An overpartition of `n` is a partition of `n` in which the first (equivalently, last)
occurrence of each distinct part may be overlined. Since `Nat.Partition` stores an
unordered multiset, the overlining data are represented by a choice of distinct part
sizes occurring in the underlying partition. The two conventions are equivalent: each
records one binary choice per distinct occurring part size, and the unordered multiset
carries no order to distinguish first from last.

## Main definitions

* `Nat.Overpartition` is an overpartition with a specified underlying partition and overlined sizes.
* `Nat.Overpartition.IsOverlined` says that a part size is overlined.
* `Nat.Overpartition.ofPartition` equips a partition with no overlined sizes.
* `Nat.Overpartition.full` equips a partition with every distinct part size overlined.

## References

* [B. Hemanthkumar and H. S. Sumanth Bharadwaj, *Arithmetic properties of
  2^α-Regular overpartition pairs*](https://arxiv.org/abs/2502.17312)
* [J. Aniceto and C. Ballantine, *Identities involving the number of missing integers in
  partitions - combinatorial proofs*](https://arxiv.org/abs/2608.00278)
* [G. Andrews and M. Ghosh Dastidar, *The Partition Pairing
  Theorems I*](https://arxiv.org/abs/2608.22291)
-/


namespace Nat

/-- An overpartition of `n`, represented by an underlying partition and its overlined part sizes. -/
@[ext]
structure Overpartition (n : ℕ) where
  /-- The underlying partition. -/
  toPartition : Partition n
  /-- The distinct part sizes that are overlined. -/
  overlines : Finset ℕ
  /-- Every overlined size occurs in the underlying partition. -/
  overlines_subset : overlines ⊆ toPartition.parts.toFinset
deriving DecidableEq

end Nat
