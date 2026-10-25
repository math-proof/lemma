/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/Overpartition.lean -/


import Def.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition
import Theorem.MathlibExtTest.Combinatorics.Enumerative.Partition.Overpartition


namespace Nat.Overpartition

def partition14 : Nat.Partition 14 :=
  Nat.Partition.ofMultiset {5, 5, 3, 1}

def overpartition14 : Nat.Overpartition 14 where
  toPartition := partition14
  overlines := {5, 1}
  overlines_subset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · show (5 : ℕ) ∈ partition14.parts.toFinset
      rw [Multiset.mem_toFinset]
      decide
    · show (1 : ℕ) ∈ partition14.parts.toFinset
      rw [Multiset.mem_toFinset]
      decide

end Nat.Overpartition
