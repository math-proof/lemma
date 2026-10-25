/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Finpartition/BasicSetPartition.lean -/

import Mathlib.Order.Partition.Finpartition
import Mathlib.Order.Interval.Finset.Nat


namespace MetaMathlibExt

/-- Basic set partition (concept `jis_sem_a7cf8b184541b1aad513e021`,
  statement `jis_a15ca13d7bcc157dc6123a58`): an ordinary `Finpartition`
  of `Finset.Icc 1 n` whose parts admit a nonincreasing initial-segment labeling. -/
def IsBasicSetPartition (n : ℕ) (P : Finpartition (Finset.Icc 1 n)) : Prop :=
  ∃ blocks : List (Finset ℕ),
    blocks.Nodup ∧
    blocks.toFinset = P.parts ∧
    (∀ B ∈ blocks, 0 < B.card) ∧
    List.Pairwise (fun earlier later => later.card ≤ earlier.card) blocks ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ blocks.length →
      (blocks.take i).foldl (· ∪ ·) (∅ : Finset ℕ) =
        Finset.Icc 1 (((blocks.take i).map Finset.card).sum)

end MetaMathlibExt
