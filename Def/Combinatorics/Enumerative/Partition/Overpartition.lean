/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Overpartition.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Structure.Combinatorics.Enumerative.Partition.Overpartition
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

namespace Overpartition

/-- `a` is overlined in the overpartition `O`. -/
def IsOverlined {n : ℕ} (O : Overpartition n) (a : ℕ) : Prop :=
  a ∈ O.overlines

/-- Equip a partition with no overlined part sizes. -/
def ofPartition {n : ℕ} (p : Partition n) : Overpartition n where
  toPartition := p
  overlines := ∅
  overlines_subset := by simp

/-- Equip a partition with every distinct occurring part size overlined. -/
def full {n : ℕ} (p : Partition n) : Overpartition n where
  toPartition := p
  overlines := p.parts.toFinset
  overlines_subset := fun _ hx => hx

end Overpartition
end Nat
